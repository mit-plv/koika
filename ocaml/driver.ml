type ptr_t = int

module CircuitHash =
  struct
    type t = Sga.tFn Sga.circuit
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

type 'tFn circuit =
  | CQuestionMark
  | CNot of ptr_t
  | CAnd of ptr_t * ptr_t
  | COr of ptr_t * ptr_t
  | CMux of ptr_t * ptr_t * ptr_t
  | CConst of bool list (* TODO: keep constants shared? *)
  | CExternal of 'tFn * ptr_t list

let dedup_circuit (cs: (Sga.tFn Sga.circuit) list) =
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
         | Sga.CQuestionMark -> CQuestionMark
         | Sga.CNot c -> CNot (aux c)
         | Sga.CAnd (c1, c2) -> CAnd (aux c1, aux c2)
         | Sga.COr (c1, c2) -> COr (aux c1, aux c2)
         | Sga.CMux (s, c1, c2) -> CMux (aux s, aux c1, aux c2)
         | Sga.CConst bs -> CConst bs
         | Sga.CExternal (fname, cargs) -> CExternal (fname, List.map aux cargs) in
       CircuitHashtbl.add object_to_ptr c ptr;
       PtrHashtbl.add ptr_to_object ptr deduplicated;
       ptr in
  let deduped = List.map aux cs in
  (* CircuitHashtbl.fold (fun k v acc -> (k, v) :: acc)  object_to_ptr [], *)
  (* PtrHashtbl.fold (fun k v acc -> (k, v) :: acc)  ptr_to_object []) *)
  (deduped, ptr_to_object)

let print_bits bs =
  "0b" ^ (String.concat "" (List.map (fun b -> if b then "1" else "0") bs))

let rec int_of_nat = function
  | Sga.O -> 0
  | Sga.S n -> succ (int_of_nat n)

let print_external = function
  | Sga.Even -> "even"
  | Sga.ReadReg n -> Printf.sprintf "Reg %d" (int_of_nat n)

let label_args c =
  match c with
  | CQuestionMark -> "?", []
  | CNot c -> "Not", [c]
  | CAnd (c1, c2) -> "And", [c1; c2]
  | COr (c1, c2) -> "Or", [c1; c2]
  | CMux (s, c1, c2) -> "Mux", [s; c1; c2]
  | CConst bs -> print_bits bs, []
  | CExternal (fname, cargs) -> print_external fname, cargs

let print_deduped (_roots, ptr_to_object) =
  Printf.printf "digraph {\n";
  PtrHashtbl.iter (fun ptr v ->
      let lbl, args = label_args v in
      Printf.printf "N%d [label=\"%s\"]\n" ptr lbl;
      List.iter (Printf.printf "N%d -> N%d\n" ptr) args)
    ptr_to_object;
  Printf.printf "}\n"

let _  = print_deduped (dedup_circuit Sga.compiled_example_ls)
