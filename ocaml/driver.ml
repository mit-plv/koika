type ptr_t = int

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
  | CMux of ptr_t * ptr_t * ptr_t
  | CConst of bool list (* TODO: keep constants shared? *)
  | CExternal of 'fn_t * ptr_t * ptr_t
  | CReadRegister of 'reg_t

let rec int_of_nat = function
  | Sga.O -> 0
  | Sga.S n -> succ (int_of_nat n)

let dedup_circuit (cs: (('a, Sga.Collatz.fn_t) Sga.circuit) list) =
  let object_to_ptr = CircuitHashtbl.create 50 in
  let ptr_to_object = PtrHashtbl.create 50 in
  let nextptr = ref 0 in
  let rec aux c =
    match CircuitHashtbl.find_opt object_to_ptr c with
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
         | Sga.CMux (_sz, s, c1, c2) -> CMux (aux s, aux c1, aux c2)
         | Sga.CConst (sz, bs) -> CConst (Sga.vect_to_list sz bs)
         | Sga.CExternal (fname, c1, c2) -> CExternal (fname, aux c1, aux c2)
         | Sga.CReadRegister r -> CReadRegister r
       in
       CircuitHashtbl.add object_to_ptr c ptr;
       PtrHashtbl.add ptr_to_object ptr deduplicated;
       ptr in
  let deduped = List.map aux cs in
  (* CircuitHashtbl.fold (fun k v acc -> (k, v) :: acc)  object_to_ptr [], *)
  (* PtrHashtbl.fold (fun k v acc -> (k, v) :: acc)  ptr_to_object []) *)
  (deduped, ptr_to_object)

let print_bits bs =
  "b" ^ (String.concat "" (List.map (fun b -> if b then "1" else "0") bs))

let string_of_fn = function
| Sga.Collatz.Even -> "even"
| Sga.Collatz.Odd -> "odd"
| Sga.Collatz.Divide -> "divide"
| Sga.Collatz.ThreeNPlusOne -> "threenplusone"

let string_of_register = function
| _ -> "R0"

let label_ptrs = function
  | CNot c -> Some ("Not", [c])
  | CAnd (c1, c2) -> Some ("And", [c1; c2])
  | COr (c1, c2) -> Some ("Or", [c1; c2])
  | CMux (s, c1, c2) -> Some ("Mux", [s; c1; c2])
  | CExternal (fname, c1, c2) -> Some (string_of_fn fname, [c1; c2])
  | CReadRegister r -> Some (Printf.sprintf "Reg %s" (string_of_register r), [])
  | _ -> None

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

let print_deduped (roots, ptr_to_object) =
  Printf.printf "digraph {\n";
  (* Printf.printf "rankdir=BT\n"; *)
  PtrHashtbl.iter (fun ptr v ->
      match label_ptrs v with
      | None -> ()
      | Some (lbl, ptrs) ->
         let args_or_ptrs = List.map (field_ptr_or_label ptr_to_object) ptrs in
         let lbl = dot_record_label lbl args_or_ptrs in
         Printf.printf "N%d [label=\"%s\", shape=\"record\"]\n" ptr lbl;
         List.iteri (fun i pl ->
             match pl with
             | Ptr ptr' -> Printf.printf "N%d:hd -> N%d:f%d\n" ptr' ptr i
             | _ -> ())
           args_or_ptrs)
    ptr_to_object;
  List.iteri (fun i rootptr ->
      Printf.printf "R%d [label=\"Register %d\", shape=\"record\"]\n" i i;
      Printf.printf "N%d:hd -> R%d\n" rootptr i)
    roots;
  Printf.printf "}\n"

let _  = print_deduped (dedup_circuit [Sga.collatz_r0_circuit])
