type ptr_t = int
type fn_t = Sga.Collatz.fn_t

module CircuitHash =
  struct
    type t = (Sga.__, Sga.Collatz.fn_t) Sga.circuit
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

type ('reg_t, 'fn_t) circuit =
  | CQuestionMark of int
  | CNot of ptr_t
  | CAnd of ptr_t * ptr_t
  | COr of ptr_t * ptr_t
  | CMux of int * ptr_t * ptr_t * ptr_t
  | CConst of bool list (* TODO: keep constants shared? *)
  | CExternal of 'fn_t * ptr_t * ptr_t
  | CReadRegister of 'reg_t
  | CAnnot of string * ptr_t

let rec int_of_nat = function
  | Sga.O -> 0
  | Sga.S n -> succ (int_of_nat n)

let string_of_coq_string chars =
  String.concat "" (List.map (String.make 1) chars)

let dedup_circuit (cs: (('a, fn_t) Sga.circuit) list) =
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
         | Sga.CQuestionMark n -> CQuestionMark (int_of_nat n)
         | Sga.CNot c -> CNot (aux c)
         | Sga.CAnd (c1, c2) -> CAnd (aux c1, aux c2)
         | Sga.COr (c1, c2) -> COr (aux c1, aux c2)
         | Sga.CMux (sz, s, c1, c2) -> CMux (int_of_nat sz, aux s, aux c1, aux c2)
         | Sga.CConst (sz, bs) -> CConst (Sga.vect_to_list sz bs)
         | Sga.CExternal (fname, c1, c2) -> CExternal (fname, aux c1, aux c2)
         | Sga.CReadRegister r -> CReadRegister r
         | Sga.CAnnot (_, annot, c) -> CAnnot (string_of_coq_string annot, aux c)
       in
       CircuitHashtbl.add circuit_to_ptr c ptr;
       PtrHashtbl.add ptr_to_object ptr deduplicated;
       ptr in
  let deduped = List.map aux cs in
  (* CircuitHashtbl.fold (fun k v acc -> (k, v) :: acc)  object_to_ptr [], *)
  (* PtrHashtbl.fold (fun k v acc -> (k, v) :: acc)  ptr_to_object []) *)
  (deduped, ptr_to_object)

let size_of_fn (f: fn_t) : int * int * int =
  (int_of_nat (Sga.Collatz.coq_Sigma f).arg1Type,
   int_of_nat (Sga.Collatz.coq_Sigma f).arg2Type,
   int_of_nat (Sga.Collatz.coq_Sigma f).retType)

let size_of_reg (r: Sga.__) : int =
  int_of_nat (Sga.Collatz.coq_R r)

let print_bits bs =
  "b" ^ (String.concat "" (List.map (fun b -> if b then "1" else "0") bs))

let string_of_fn = function
| Sga.Collatz.Even -> "even"
| Sga.Collatz.Odd -> "odd"
| Sga.Collatz.Divide -> "divide"
| Sga.Collatz.ThreeNPlusOne -> "threenplusone"

let string_of_register = function
| _ -> "R0"

let rec obj_children = function
  | CNot c -> [c]
  | CAnd (c1, c2) -> [c1; c2]
  | COr (c1, c2) -> [c1; c2]
  | CMux (_sz, s, c1, c2) -> [s; c1; c2]
  | CExternal (_fname, c1, c2) -> [c1; c2]
  | CReadRegister _r -> []
  | CAnnot (_annot, c) -> [c]
  | CQuestionMark _ -> []
  | CConst _ -> []

let ptrhashtbl_update tbl k v_dflt v_fn =
  PtrHashtbl.replace tbl k
    (v_fn (match PtrHashtbl.find_opt tbl k with
           | Some v -> v
           | None -> v_dflt))

let rec compute_parents ptr_to_object =
  let ptr_to_parents = PtrHashtbl.create 50 in
  PtrHashtbl.iter (fun _ptr obj ->
      List.iter (fun child ->
          ptrhashtbl_update ptr_to_parents child []
            (fun children -> child :: children))
        (obj_children obj))
    ptr_to_object;
  ptr_to_parents

let rec label_ptrs p2o p2p = function
  | CNot c -> Some ("Not", [c], [])
  | CAnd (c1, c2) -> Some ("And", [c1; c2], [])
  | COr (c1, c2) -> Some ("Or", [c1; c2], [])
  | CMux (_sz, s, c1, c2) -> Some ("Mux", [s; c1; c2], [])
  | CExternal (fname, c1, c2) -> Some (string_of_fn fname, [c1; c2], [])
  | CReadRegister r -> Some (Printf.sprintf "Reg %s" (string_of_register r), [], [])
  | CAnnot (annot, c) ->
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
  | CQuestionMark _ -> None
  | CConst _ -> None

type ptr_or_label =
  | Ptr of int
  | Label of string

let dot_field_label i pl =
  Printf.sprintf "<f%d> %s" i (match pl with
                               | Label lbl -> lbl
                               | Ptr _ -> "·")

let field_ptr_or_label ptr_to_object ptr =
  match PtrHashtbl.find ptr_to_object ptr with
  | CQuestionMark n -> Label (Printf.sprintf "?'%d" n)
  | CConst bs -> Label (print_bits bs)
  | _ -> Ptr ptr

let dot_record_label head args =
  let fields = List.mapi dot_field_label args in
  String.concat "|" (Printf.sprintf "<hd> %s" head :: fields)

(* let cleanup_deduped ptr_to_object =
 *   let ptr_to_children = PtrHashtbl.create 50 in *)

let print_deduped (roots, ptr_to_object) =
  let ptr_to_parents = compute_parents ptr_to_object in

  let ptr_to_graph_data = PtrHashtbl.create 50 in
  let orphaned = ref [] in
    PtrHashtbl.iter (fun ptr v ->
      match label_ptrs ptr_to_object ptr_to_parents v with
      | None -> ()
      | Some (lbl, children, removed) ->
         List.iter (fun ptr -> orphaned := ptr :: !orphaned) removed;
         PtrHashtbl.add ptr_to_graph_data ptr (lbl, children))
    ptr_to_object;
  List.iter (fun ptr -> PtrHashtbl.remove ptr_to_graph_data ptr) !orphaned;

  Printf.printf "digraph {\n";
  (* Printf.printf "rankdir=BT\n"; *)
  PtrHashtbl.iter (fun ptr (lbl, children) ->
      let args_or_ptrs = List.map (field_ptr_or_label ptr_to_object) children in
      let lbl = dot_record_label lbl args_or_ptrs in
      Printf.printf "N%d [label=\"%s\", shape=\"record\"]\n" ptr lbl;
      List.iteri (fun i pl ->
          match pl with
          | Ptr ptr' -> Printf.printf "N%d:hd -> N%d:f%d\n" ptr' ptr i
          | _ -> ())
        args_or_ptrs)
    ptr_to_graph_data;
  List.iteri (fun i rootptr ->
      Printf.printf "R%d [label=\"Register %d\", shape=\"record\"]\n" i i;
      Printf.printf "N%d:hd -> R%d\n" rootptr i)
    roots;
  Printf.printf "}\n"

let _  = print_deduped (dedup_circuit [Sga.collatz_r0_circuit])
