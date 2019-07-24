open Common
open SGALib

let primitive_name = function
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
  | SGA.UIntPlus _sz -> "Concat"

let fun_name = function
  | CustomFn fn -> fn
  | PrimFn fn -> primitive_name fn

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
       (* More than one node pointing to this annotation: don't merge *)
       Some (annot, [c], [])
     else
       (* Exactly one node pointing to this annotation: try to merge it with the
        node it qualifies *)
       (match label_ptrs p2o p2p (PtrHashtbl.find p2o c) with
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

let field_ptr_or_label ptr_to_object ptr =
  match PtrHashtbl.find ptr_to_object ptr with
  (* | CQuestionMark n -> Label (Printf.sprintf "?'%d" n) *)
  | CConst bs -> Label (Util.string_of_bits bs)
  | _ -> Ptr ptr

let dot_record_label head args =
  let fields = List.mapi field_label args in
  String.concat "|" (Printf.sprintf "<hd> %s" head :: fields)

let print_dot_file out Graphs.{ graph_roots = roots; graph_ptrs = ptr2obj } =
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

  Printf.fprintf out "digraph {\n";
  (* Printf.fprintf out "rankdir=BT\n"; *)
  PtrHashtbl.iter (fun ptr (lbl, children) ->
      let args_or_ptrs = List.map (field_ptr_or_label ptr2obj) children in
      let lbl = dot_record_label lbl args_or_ptrs in
      Printf.fprintf out "N%d [label=\"%s\", shape=\"record\"]\n" ptr lbl;
      List.iteri (fun i pl ->
          match pl with
          | Ptr ptr' -> Printf.fprintf out "N%d:hd -> N%d:f%d\n" ptr' ptr i
          | _ -> ())
        args_or_ptrs)
    ptr_to_graph_data;
  List.iteri (fun i { root_reg; root_ptr } ->
      Printf.fprintf out "R%d [label=\"Register %s\", shape=\"record\"]\n" i root_reg.reg_name;
      Printf.fprintf out "N%d:hd -> R%d\n" root_ptr i)
    roots;
  Printf.fprintf out "}\n"

let main out g =
  print_dot_file out g
