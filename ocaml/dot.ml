open Common
open SGALib

let bits_primitive_name = function
  | SGA.Sel _logsz -> "Sel"
  | SGA.Part (_logsz, _width) -> "Part"
  | SGA.And _sz -> "And"
  | SGA.Or _sz -> "Or"
  | SGA.Not _sz -> "Not"
  | SGA.Lsl (_sz, _places) -> "Lsl"
  | SGA.Lsr (_sz, _places) -> "Lsr"
  | SGA.Eq _sz -> "Eq"
  | SGA.Concat (_sz1, _sz2) -> "Concat"
  | SGA.ZExtL (_sz, _nzeroes) -> "ZExtL"
  | SGA.ZExtR (_sz, _nzeroes) -> "ZExtR"
  | SGA.UIntPlus _sz -> "Plus"

let rec label_ptrs tag_to_parents = function
  | CNot c -> Some ("Not", [c], [])
  | CAnd (c1, c2) -> Some ("And", [c1; c2], [])
  | COr (c1, c2) -> Some ("Or", [c1; c2], [])
  | CMux (_sz, s, c1, c2) -> Some ("Mux", [s; c1; c2], [])
  | CExternal (ffi, c1, c2) ->
     Some
       (match ffi.ffi_name with
        | CustomFn fn -> (fn, [c1; c2], [])
        | PrimFn (SGA.BitsFn fn) -> (bits_primitive_name fn, [c1; c2], [])
        | PrimFn (SGA.StructFn (sg, op)) ->
           let sg = SGALib.Util.struct_sig_of_sga_struct_sig' sg in
           match op with
           | SGA.Init -> (Printf.sprintf "%s {}" sg.struct_name, [], [])
           | SGA.Do (ac, idx) ->
              let field, _tau = SGALib.Util.list_nth sg.struct_fields idx in
              match ac with
              | SGA.Get -> (Printf.sprintf "%s.%s" sg.struct_name field, [c1], [])
              | SGA.Sub -> (Printf.sprintf "%s / %s <-" sg.struct_name field, [c1; c2], []))
  | CReadRegister r -> Some (Printf.sprintf "Reg %s" r.reg_name, [], [])
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
  Printf.sprintf "<f%d> %s" i (match pl with
                               | Label lbl -> lbl
                               | Ptr _ -> "·")

let field_ptr_or_label (c: _ circuit) =
  match c.node with
  (* | CQuestionMark n -> Label (Printf.sprintf "?'%d" n) *)
  | CConst bs -> Label (Util.string_of_bits bs)
  | _ -> Ptr c.tag

let dot_record_label head args =
  let fields = List.mapi field_label args in
  let head = (if head = "constant_value_from_source" then "" else head) in
  String.concat "|" (Printf.sprintf "<hd> %s" head :: fields)

let print_dot_file out Graphs.{ graph_roots = roots; graph_nodes = circuits } =
  let tag_to_parents = compute_parents circuits in
  let tag_to_graph_data = Hashtbl.create 50 in
  let orphaned = ref [] in
  List.iter (fun Hashcons.{ node; tag; _ } ->
      match label_ptrs tag_to_parents node with
      | None -> ()
      | Some (lbl, children, removed) ->
         List.iter (fun c -> orphaned := c :: !orphaned) removed;
         Hashtbl.add tag_to_graph_data tag (lbl, children))
    circuits;
  List.iter (fun c -> Hashtbl.remove tag_to_graph_data c.Hashcons.tag) !orphaned;

  Printf.fprintf out "digraph {\n";
  (* Printf.fprintf out "rankdir=BT\n"; *)
  Hashtbl.iter (fun ptr (lbl, children) ->
      let args_or_ptrs = List.map field_ptr_or_label children in
      let lbl = dot_record_label lbl args_or_ptrs in
      Printf.fprintf out "N%d [label=\"%s\", shape=\"record\"]\n" ptr lbl;
      List.iteri (fun i pl ->
          match pl with
          | Ptr ptr' -> Printf.fprintf out "N%d:hd -> N%d:f%d\n" ptr' ptr i
          | _ -> ())
        args_or_ptrs)
    tag_to_graph_data;
  List.iteri (fun i { root_reg; root_circuit } ->
      Printf.fprintf out "R%d [label=\"Register %s\", shape=\"record\"]\n" i root_reg.reg_name;
      Printf.fprintf out "N%d:hd -> R%d\n" root_circuit.tag i)
    roots;
  Printf.fprintf out "}\n"

let main out g =
  print_dot_file out g
