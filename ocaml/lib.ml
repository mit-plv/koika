type ptr_t = int
type size_t = int
type sga_circuit = (Sga.__, Sga.__ Sga.interop_fn_t) Sga.circuit

module CircuitHash =
  struct
    type t = sga_circuit
    let equal o1 o2 = o1 == o2
    let hash o = Hashtbl.hash o
  end

module PtrHash =
  struct
    type t = ptr_t
    let equal p1 p2 = p1 = p2
    let hash p = Hashtbl.hash p
  end

module CircuitHashtbl = Hashtbl.Make(CircuitHash)
module PtrHashtbl = Hashtbl.Make(PtrHash)

type bits_const = {
    bs_size: size_t;
    bs_bits: bool list;
    bs_val: int;
  }

type fun_id_t =
  | CustomFn of string
  | PrimFn of Sga.prim_fn_t

type ffi_signature = {
    ffi_name: fun_id_t;
    ffi_arg1size: size_t;
    ffi_arg2size: size_t;
    ffi_retsize: size_t
  }

type reg_signature = {
    reg_name: string;
    reg_size: size_t;
    reg_init_val: bits_const;
  }

type circuit_root = {
    root_reg: reg_signature;
    root_ptr: ptr_t;
  }

type circuit =
  (* | CQuestionMark of size_t *)
  | CNot of ptr_t
  | CAnd of ptr_t * ptr_t
  | COr of ptr_t * ptr_t
  | CMux of size_t * ptr_t * ptr_t * ptr_t
  | CConst of bits_const (* TODO: keep constants shared? *)
  | CExternal of ffi_signature * ptr_t * ptr_t
  | CReadRegister of reg_signature
  | CAnnot of size_t * string * ptr_t

type dedup_result = {
    dedup_roots: circuit_root list;
    dedup_ptrs: circuit PtrHashtbl.t
  }

let primitive_name = function
  | Sga.Sel logsz -> "Sel"
  | Sga.Part (logsz, width) -> "Part"
  | Sga.And sz -> "And"
  | Sga.Or sz -> "Or"
  | Sga.Not sz -> "Not"
  | Sga.Lsl (sz, places) -> "Lsl"
  | Sga.Lsr (sz, places) -> "Lsr"
  | Sga.Eq sz -> "Eq"
  | Sga.Concat (sz1, sz2) -> "Concat"
  | Sga.ZExtL (sz, nzeroes) -> "ZExtL"
  | Sga.ZExtR (sz, nzeroes) -> "ZExtR"

let string_of_bits bs =
  let bitstring = String.concat "" (List.rev_map (fun b -> if b then "1" else "0") bs.bs_bits) in
  Printf.sprintf "%d'b%s" bs.bs_size bitstring

let string_of_coq_string chars =
  String.concat "" (List.map (String.make 1) chars)

let fun_name = function
  | CustomFn fn -> fn
  | PrimFn fn -> primitive_name fn

let ffi_sig_of_fn (pkg: Sga.verilogPackage) fn =
  let ffi_name, fsig = match fn with
    | Sga.PrimFn fn ->
       PrimFn fn,
       Sga.prim_Sigma fn
    | Sga.CustomFn fn ->
       CustomFn (string_of_coq_string (pkg.vp_custom_fn_names fn)),
       pkg.vp_custom_fn_types fn in
  { ffi_name;
    ffi_arg1size = fsig.arg1Type;
    ffi_arg2size = fsig.arg2Type;
    ffi_retsize = fsig.retType }

let bits_const_of_bits sz bs =
  { bs_size = sz;
    bs_bits = Sga.vect_to_list sz bs;
    bs_val = Sga.Bits.to_nat sz bs }

let reg_sig_of_rname (pkg: Sga.verilogPackage) r =
  let sz = pkg.vp_reg_types r in
  { reg_name = string_of_coq_string (pkg.vp_reg_names r);
    reg_size = sz;
    reg_init_val = bits_const_of_bits sz (pkg.vp_reg_init r) }

let dedup_circuit (pkg: Sga.verilogPackage) : dedup_result =
  let circuit_to_ptr = CircuitHashtbl.create 50 in
  let ptr_to_object = PtrHashtbl.create 50 in
  let nextptr = ref 0 in
  let rec aux (c: _ Sga.circuit) =
    match CircuitHashtbl.find_opt circuit_to_ptr c with
    | Some ptr -> ptr
    | None ->
       let ptr = !nextptr in
       incr nextptr;
       let deduplicated =
         match c with
         (* | Sga.CQuestionMark n ->
          *    CQuestionMark n *)
         | Sga.CNot c ->
            CNot (aux c)
         | Sga.CAnd (c1, c2) ->
            CAnd (aux c1, aux c2)
         | Sga.COr (c1, c2) ->
            COr (aux c1, aux c2)
         | Sga.CMux (sz, s, c1, c2) ->
            CMux (sz, aux s, aux c1, aux c2)
         | Sga.CConst (sz, bs) ->
            CConst (bits_const_of_bits sz bs)
         | Sga.CExternal (fn, c1, c2) ->
            CExternal (ffi_sig_of_fn pkg fn, aux c1, aux c2)
         | Sga.CReadRegister r ->
            CReadRegister (reg_sig_of_rname pkg r)
         | Sga.CAnnot (sz, annot, c) ->
            CAnnot (sz, string_of_coq_string annot, aux c)
       in
       CircuitHashtbl.add circuit_to_ptr c ptr;
       PtrHashtbl.add ptr_to_object ptr deduplicated;
       ptr in
  (* CircuitHashtbl.fold (fun k v acc -> (k, v) :: acc)  object_to_ptr [], *)
  (* PtrHashtbl.fold (fun k v acc -> (k, v) :: acc)  ptr_to_object []) *)
  { dedup_roots = List.map (fun reg ->
                      let c = Sga.getenv pkg.vp_reg_Env pkg.vp_circuit reg in
                      { root_reg = reg_sig_of_rname pkg reg;
                        root_ptr = aux c })
                    pkg.vp_reg_finite.finite_elems;
    dedup_ptrs = ptr_to_object }

let obj_children = function
  | CNot c -> [c]
  | CAnd (c1, c2) -> [c1; c2]
  | COr (c1, c2) -> [c1; c2]
  | CMux (_sz, s, c1, c2) -> [s; c1; c2]
  | CExternal (_fn, c1, c2) -> [c1; c2]
  | CReadRegister _r -> []
  | CAnnot (_sz, _annot, c) -> [c]
  (* | CQuestionMark _ -> [] *)
  | CConst _ -> []

let ptrhashtbl_update tbl k v_dflt v_fn =
  PtrHashtbl.replace tbl k
    (v_fn (match PtrHashtbl.find_opt tbl k with
           | Some v -> v
           | None -> v_dflt))

let compute_parents ptr_to_object =
  let ptr_to_parents = PtrHashtbl.create 50 in
  PtrHashtbl.iter (fun _ptr obj ->
      List.iter (fun child ->
          ptrhashtbl_update ptr_to_parents child []
            (fun children -> child :: children))
        (obj_children obj))
    ptr_to_object;
  ptr_to_parents

module Dot = struct
  let rec label_ptrs p2o p2p = function
    | CNot c -> Some ("Not", [c], [])
    | CAnd (c1, c2) -> Some ("And", [c1; c2], [])
    | COr (c1, c2) -> Some ("Or", [c1; c2], [])
    | CMux (_sz, s, c1, c2) -> Some ("Mux", [s; c1; c2], [])
    | CExternal (ffi, c1, c2) -> Some (fun_name ffi.ffi_name, [c1; c2], [])
    | CReadRegister r -> Some (Printf.sprintf "Reg %s" r.reg_name, [], [])
    | CAnnot (_sz, annot, c) ->
       let nparents = List.length (PtrHashtbl.find p2p c) in
       if nparents = 0 then
         failwith "Unreachable node"
       else if nparents > 1 then
         (* More than one node pointing to this annotation: don't merge*)
         Some (annot, [c], [])
       else
         (* Exactly one node pointing to this annotation: try to merge it with the
          node it qualifies *)
         (match label_ptrs p2o p2p (PtrHashtbl.find p2o c) with
          | Some (sublabel, subcircuits, removed) ->
             Some (sublabel ^ "[" ^ annot ^ "]", subcircuits, c :: removed)
          | None -> Some (annot, [c], []))
    (* | CQuestionMark _ -> None *)
    | CConst _ -> None

  type ptr_or_label =
    | Ptr of int
    | Label of string

  let field_label i pl =
    Printf.sprintf "<f%d> %s" i (match pl with
                                 | Label lbl -> lbl
                                 | Ptr _ -> "·")

  let field_ptr_or_label ptr_to_object ptr =
    match PtrHashtbl.find ptr_to_object ptr with
    (* | CQuestionMark n -> Label (Printf.sprintf "?'%d" n) *)
    | CConst bs -> Label (string_of_bits bs)
    | _ -> Ptr ptr

  let dot_record_label head args =
    let fields = List.mapi field_label args in
    String.concat "|" (Printf.sprintf "<hd> %s" head :: fields)

  let print_dot_file { dedup_roots = roots; dedup_ptrs = ptr2obj } =
    let ptr_to_parents = compute_parents ptr2obj in
    let ptr_to_graph_data = PtrHashtbl.create 50 in
    let orphaned = ref [] in
    PtrHashtbl.iter (fun ptr v ->
        match label_ptrs ptr2obj ptr_to_parents v with
        | None -> ()
        | Some (lbl, children, removed) ->
           List.iter (fun ptr -> orphaned := ptr :: !orphaned) removed;
           PtrHashtbl.add ptr_to_graph_data ptr (lbl, children))
      ptr2obj;
    List.iter (fun ptr -> PtrHashtbl.remove ptr_to_graph_data ptr) !orphaned;

    Printf.printf "digraph {\n";
    (* Printf.printf "rankdir=BT\n"; *)
    PtrHashtbl.iter (fun ptr (lbl, children) ->
        let args_or_ptrs = List.map (field_ptr_or_label ptr2obj) children in
        let lbl = dot_record_label lbl args_or_ptrs in
        Printf.printf "N%d [label=\"%s\", shape=\"record\"]\n" ptr lbl;
        List.iteri (fun i pl ->
            match pl with
            | Ptr ptr' -> Printf.printf "N%d:hd -> N%d:f%d\n" ptr' ptr i
            | _ -> ())
          args_or_ptrs)
      ptr_to_graph_data;
    List.iteri (fun i { root_reg; root_ptr } ->
        Printf.printf "R%d [label=\"Register %s\", shape=\"record\"]\n" i root_reg.reg_name;
        Printf.printf "N%d:hd -> R%d\n" root_ptr i)
      roots;
    Printf.printf "}\n"
end
