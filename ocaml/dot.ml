open Common
open SGALib
open SGALib.Graphs
open Printf

let bits1_name =
  let open SGA.PrimTyped in
  function
  | Not _sz -> "Not"
  | ZExtL (_sz, _width) -> "ZExtL"
  | ZExtR (_sz, _width) -> "ZExtR"
  | Part (_logsz, _offset, _width) -> "Part"

let bits2_name =
  let open SGA.PrimTyped in
  function
  | Sel _logsz -> "Sel"
  | PartSubst (_logsz, _offset, _width) -> "PartSubst"
  | IndexedPart (_logsz, _width) -> "IndexedPart"
  | And _sz -> "And"
  | Or _sz -> "Or"
  | Lsl (_sz, _places) -> "Lsl"
  | Lsr (_sz, _places) -> "Lsr"
  | EqBits _sz -> "EqBits"
  | Concat (_sz1, _sz2) -> "Concat"
  | UIntPlus _sz -> "Plus"
  | UIntLt _sz -> "Lt"

let rec label_ptrs tag_to_parents = function
  | CNot c -> Some ("Not", [c], [])
  | CAnd (c1, c2) -> Some ("And", [c1; c2], [])
  | COr (c1, c2) -> Some ("Or", [c1; c2], [])
  | CMux (_sz, s, c1, c2) -> Some ("Mux", [s; c1; c2], [])
  | CUnop (fn, c) -> Some (bits1_name fn, [c], [])
  | CBinop (fn, c1, c2) -> Some (bits2_name fn, [c1; c2], [])
  | CExternal (ffi, c) -> Some (ffi.ffi_name, [c], [])
  | CReadRegister r -> Some (sprintf "Reg %s" r.reg_name, [], [])
  | CBundle (_, _) -> None (* FIXME *)
  | CBundleRef (_, _, _) -> None (* FIXME *)
  | CAnnot (_sz, annot, c) ->
     let nparents = List.length (Hashtbl.find tag_to_parents c.tag) in
     if nparents = 0 then
       failwith "Unreachable node"
     else if nparents > 1 then
       (* More than one node pointing to this annotation: don't merge *)
       Some (annot, [c], [])
     else
       (* Exactly one node pointing to this annotation: try to merge it with the
        node it qualifies *)
       (match label_ptrs tag_to_parents c.node with
        | Some (sublabel, subcircuits, removed) ->
           Some (sublabel ^ "[" ^ annot ^ "]", subcircuits, c :: removed)
        | None -> Some (annot, [c], []))
  | CConst _ -> None

type ptr_or_label =
  | Ptr of int
  | Label of string

let field_label i pl =
  sprintf "<f%d> %s" i (match pl with
                        | Label lbl -> lbl
                        | Ptr _ -> "·")

let field_ptr_or_label (c: circuit) =
  match c.node with
  (* | CQuestionMark n -> Label (sprintf "?'%d" n) *)
  | CConst bs -> Label (Util.string_of_bits bs)
  | _ -> Ptr c.tag

let dot_record_label head args =
  let fields = List.mapi field_label args in
  let head = (if head = "constant_value_from_source" then "" else head) in
  String.concat "|" (sprintf "<hd> %s" head :: fields)

let subcircuits = function
  | CNot c -> [c]
  | CAnd (c1, c2) -> [c1; c2]
  | COr (c1, c2) -> [c1; c2]
  | CMux (_sz, s, c1, c2) -> [s; c1; c2]
  | CUnop (_, c) -> [c]
  | CBinop (_, c1, c2) -> [c1; c2]
  | CExternal (_, c) -> [c]
  | CReadRegister _r -> []
  | CBundle (_) -> [] (* FIXME *)
  | CBundleRef (_, _, _) -> [] (* FIXME *)
  | CAnnot (_sz, _annot, c) -> [c]
  | CConst _ -> []

let hashtbl_update tbl k v_dflt v_fn =
  Hashtbl.replace tbl k
    (v_fn (match Hashtbl.find_opt tbl k with
           | Some v -> v
           | None -> v_dflt))

let compute_parents (circuits: circuit list) =
  let tag_to_parents = Hashtbl.create 50 in
  List.iter (fun c ->
      List.iter (fun (child: circuit) ->
          hashtbl_update tag_to_parents child.tag []
            (fun children -> child :: children))
        (subcircuits c.Hashcons.node))
    circuits;
  tag_to_parents

let print_dot_file out Graphs.{ graph_roots = roots; graph_nodes = circuits } =
  let tag_to_parents = compute_parents circuits in
  let tag_to_graph_data = Hashtbl.create 50 in
  let orphaned = ref [] in
  List.iter (fun Hashcons.{ node; tag; _ } ->
      match label_ptrs tag_to_parents node with
      | None -> ()
      | Some (lbl, children, removed) ->
         orphaned := List.rev_append removed !orphaned;
         Hashtbl.add tag_to_graph_data tag (lbl, children))
    circuits;
  List.iter (fun c -> Hashtbl.remove tag_to_graph_data c.Hashcons.tag) !orphaned;

  fprintf out "digraph {\n";
  (* fprintf out "rankdir=BT\n"; *)
  Hashtbl.iter (fun ptr (lbl, children) ->
      let args_or_ptrs = List.map field_ptr_or_label children in
      let lbl = dot_record_label lbl args_or_ptrs in
      fprintf out "N%d [label=\"%s\", shape=\"record\"]\n" ptr lbl;
      List.iteri (fun i pl ->
          match pl with
          | Ptr ptr' -> fprintf out "N%d:hd -> N%d:f%d\n" ptr' ptr i
          | _ -> ())
        args_or_ptrs)
    tag_to_graph_data;
  List.iteri (fun i { root_reg; root_circuit } ->
      fprintf out "R%d [label=\"Register %s\", shape=\"record\"]\n" i root_reg.reg_name;
      fprintf out "N%d:hd -> R%d\n" root_circuit.tag i)
    roots;
  fprintf out "}\n"

let main out g =
  print_dot_file out g
