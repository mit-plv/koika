open Common
open SGALib
open Printf

let bits_primitive_name = function
  | SGA.Sel _logsz -> "Sel"
  | SGA.Part (_logsz, _offset, _width) -> "Part"
  | SGA.PartSubst (_logsz, _offset, _width) -> "PartSubst"
  | SGA.IndexedPart (_logsz, _width) -> "IndexedPart"
  | SGA.And _sz -> "And"
  | SGA.Or _sz -> "Or"
  | SGA.Not _sz -> "Not"
  | SGA.Lsl (_sz, _places) -> "Lsl"
  | SGA.Lsr (_sz, _places) -> "Lsr"
  | SGA.EqBits _sz -> "EqBits"
  | SGA.Concat (_sz1, _sz2) -> "Concat"
  | SGA.ZExtL (_sz, _width) -> "ZExtL"
  | SGA.ZExtR (_sz, _width) -> "ZExtR"
  | SGA.UIntPlus _sz -> "Plus"
  | SGA.UIntLt _sz -> "Lt"

let rec label_ptrs tag_to_parents = function
  | CNot c -> Some ("Not", [c], [])
  | CAnd (c1, c2) -> Some ("And", [c1; c2], [])
  | COr (c1, c2) -> Some ("Or", [c1; c2], [])
  | CMux (_sz, s, c1, c2) -> Some ("Mux", [s; c1; c2], [])
  | CExternal (ffi, c1, c2) ->
     Some
       (match ffi.ffi_name with
        | CustomFn fn -> (fn, [c1; c2], [])
        | PrimFn (SGA.DisplayFn fn) ->
           ((match fn with
             | SGA.DisplayUtf8 _ -> "DisplayUtf8"
             | SGA.DisplayValue _ -> "DisplayValue"),
            [c1; c2], [])
        | PrimFn (SGA.BitsFn fn) ->
           (bits_primitive_name fn, [c1; c2], [])
        | PrimFn (SGA.ConvFn (tau, fn)) ->
           let open SGA in
           let op_name = match fn with
             | Eq -> "eq"
             | Init -> "init"
             | Pack -> "pack"
             | Unpack -> "unpack"
             | Ignore -> "ignore" in
           ((match tau with
             | Bits_t sz -> sprintf "bits_%s<%d>" op_name sz
             | Enum_t sg -> sprintf "enum_%s<%s>" op_name (SGALib.Util.string_of_coq_string sg.enum_name)
             | Struct_t sg -> sprintf "struct_%s<%s>" op_name (SGALib.Util.string_of_coq_string sg.struct_name)),
            [c1; c2], [])
        | PrimFn (SGA.StructFn (sg, ac, idx)) ->
           let sg = SGALib.Util.struct_sig_of_sga_struct_sig sg in
           let field, _tau = SGALib.Util.list_nth sg.struct_fields idx in
           match ac with
           | SGA.GetField -> (sprintf "%s.%s" sg.struct_name field, [c1; c2], [])
           | SGA.SubstField -> (sprintf "%s / %s <-" sg.struct_name field, [c1; c2], []))
  | CReadRegister r -> Some (sprintf "Reg %s" r.reg_name, [], [])
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

let field_ptr_or_label (c: _ circuit) =
  match c.node with
  (* | CQuestionMark n -> Label (sprintf "?'%d" n) *)
  | CConst bs -> Label (Util.string_of_bits bs)
  | _ -> Ptr c.tag

let dot_record_label head args =
  let fields = List.mapi field_label args in
  let head = (if head = "constant_value_from_source" then "" else head) in
  String.concat "|" (sprintf "<hd> %s" head :: fields)

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
