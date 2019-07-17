open Lib

(* Phase I: IO declarations

   In our circuit we don't have inputs and outputs specified from the
   Coq side. We decide to give direct access to each register. For
   each register of width bitwidth we create:
      (1) an output wire reading the register named reg__data
      (2) an input wire to order overwriting of the data in the register.
      The wire is named reg__overwrite
      (3) an input wire carrying the data to put in the register in case of overwrite.
      The wire is named reg__overwrite__data
   We also need a clock and a reset signal.

 *)

type io_decl =
 | Input of string * int
 | Output of string * int

let io_decl_to_string (io_decl:io_decl) =
  match io_decl with
  | Input (w, sz) -> if sz = 1
                     then "input " ^ w
                     else "input " ^ "[" ^ string_of_int (sz-1) ^ ":0] " ^ w
  | Output (w, sz) -> if sz = 1
                     then "output " ^ w
                     else "output " ^ "[" ^ string_of_int (sz-1) ^ ":0] " ^ w

type io_decls = io_decl list


let io_from_reg (root: circuit_root) : io_decls =
  let reg_name = root.root_reg.reg_name in
  let reg_size = root.root_reg.reg_size in
  [
    Input (reg_name ^ "__overwrite_data", 1);
    Input (reg_name ^ "__overwrite", reg_size);
    Output (reg_name ^ "__data", reg_size)
  ]
let clock_and_reset : io_decls =
  [
    Input ("clock", 1);
    Input ("reset", 1);
  ]

let io_declarations (circuit: dedup_result) : io_decls =
  clock_and_reset @ List.flatten (List.map io_from_reg (circuit.dedup_roots))


(* Phase II: Internal declarations


   We declare the internal registers, and one wire per subcircuit
   a.k.a nodes of (circuit_nets: circuit PtrHashtbl.t).  The signal
   are all named __inter_n except for the one where a named have been
   given by the user where we name them givenname__inter_n. The sizes
   of registers and wires are also declared in that phase.

 *)
type internal_decl =
 | Reg of string * int
 | Wire of string * int

let internal_decl_to_string (internal_decl: internal_decl) =
  match internal_decl with
  | Reg (r, sz) ->  if sz = 1
                     then "reg " ^ r
                     else "reg " ^ "[" ^ string_of_int (sz-1) ^ ":0] " ^ r
  | Wire (w, sz) ->  if sz = 1
                     then "wire " ^ w
                     else "wire " ^ "[" ^ string_of_int (sz-1) ^ ":0] " ^ w

type internal_decls = internal_decl list


let internal_decl_for_reg (root: circuit_root) =
  let reg_name = root.root_reg.reg_name in
  let reg_size = root.root_reg.reg_size in
  Reg(reg_name,reg_size)

let internal_decl_for_net
      (environment: string PtrHashtbl.t)
      (gensym : int ref)
      (circuit_nets: circuit PtrHashtbl.t)
      (ptr: ptr_t)
  =
  let name_ptr = !gensym in
  gensym := !gensym + 1;
  let name_net = "__inter_" ^ (string_of_int name_ptr) in
  PtrHashtbl.add environment ptr name_net;
  match PtrHashtbl.find_opt circuit_nets ptr with
  | None -> assert false        (* This function is only called on ptr in the circuit *)
  | Some node -> (match node with
                  | CNot _
                    | CAnd (_, _)
                    | COr (_, _) ->   Wire(name_net, 1)
                  | CQuestionMark n
                    | CMux (n, _, _, _) -> Wire(name_net, n)
                  | CAnnot (n, name , _) ->  Wire(name ^ name_net, n) (* Prefix with the name given by the user *)
                  | CConst l -> Wire(name_net, l.bs_size)
                  | CExternal (ffi_sig, _, _) -> Wire(name_net, ffi_sig.ffi_retsize)
                  | CReadRegister r_sig -> Wire(name_net, r_sig.reg_size)
                  )

let internal_declarations (environment: string PtrHashtbl.t) (circuit: dedup_result) =
  let gensym = ref 0 in
  let reg_declarations = List.map internal_decl_for_reg (circuit.dedup_roots) in
  let internal_declarations = List.map
                                (internal_decl_for_net
                                   environment
                                   gensym
                                   (circuit.dedup_ptrs))
                                (List.of_seq (PtrHashtbl.to_seq_keys circuit.dedup_ptrs))
  in
  reg_declarations @ internal_declarations


(* Phase III: Continuous assignments

   Every node in the netlist (circuit_nets: circuit PtrHashtbl.t)
   corresponds to one verilog assign statement that is declaring how
   the left hand side wire gets computed from registers and wires.

   For custom functions we create an instance of the module in verilog
   for each such CustomFn encountered.

 *)
type expression =
  | EQuestionMark of size_t
  | ENot of string
  | EAnd of string * string
  | EOr of string * string
  | EMux of size_t * string * string * string
  | EConst of string
  | EExternal of ffi_signature * string * string
  | EReadRegister of string
  | EAnnot of size_t * string * string

type assignment = string * expression (* LHS, RHS *)

let assignment_to_string (gensym: int ref) (assignment: assignment) =
  let (lhs,expr) = assignment in
  let default_left = "assign " ^ lhs ^ " = " in
  (match expr with
   | EQuestionMark _ -> default_left
   | ENot n -> default_left ^ "~" ^ n
   | EAnd (arg1, arg2) -> default_left ^ arg1 ^ " & " ^ arg2
   | EOr (arg1, arg2) -> default_left ^ arg1 ^ " | " ^ arg2
   | EMux (_, sel, t, f) -> default_left ^ sel ^ " ? " ^ t ^ " : " ^ f
   | EConst s -> default_left ^ s
   | EExternal (ffi, arg1, arg2) ->
      let fct_name = (ffi.ffi_name) in
      (match fct_name with
       | CustomFn s -> let number_s = !gensym in
                       gensym := !gensym + 1 ;
                       s ^ (s ^ "__instance__" ^ string_of_int number_s) ^
                         "(" ^ arg1 ^ ", " ^ arg2 ^ "," ^ lhs ^ ")"
       | PrimFn typePrim ->
          (match typePrim with
           | Sga.Sel _ -> default_left ^ arg1 ^ "[" ^ arg2 ^ "]"
           | Sga.Part (_, _) -> (??)
           | Sga.And _ ->  default_left ^ arg1 ^ " & " ^ arg2
           | Sga.Or _ -> default_left ^ arg1 ^ " | " ^ arg2
           | Sga.Not _ -> default_left ^ "~" ^ arg1
           | Sga.Lsl (_, _) -> default_left ^ arg1 ^ " << " ^ arg2
           | Sga.Lsr (_, _) -> default_left ^ arg1 ^ " >> " ^ arg2
           | Sga.Eq _ -> default_left ^ arg1 ^ " == " ^ arg2
           | Sga.Concat (_, _) -> default_left ^ "{" ^ arg1 ^ ", " ^ arg2 ^ "}"
           | Sga.ZExtL (_, _) -> (??) (* TODO: convince clement that those are not needed as primitive *)
           | Sga.ZExtR (_, _) -> (??) (* TODO: convince clement that those are not needed as primitive *)
          )
      )
   | EReadRegister r -> default_left ^ r
   | EAnnot (_, _, rhs) -> default_left ^ rhs) ^ ";"



type continous_assignments = assignment list


let assignment_node
      (environment: string PtrHashtbl.t)
      (circuit_nets: circuit PtrHashtbl.t)
      (ptr: ptr_t)
  : assignment
  =
  let node = PtrHashtbl.find circuit_nets ptr in (* The ptr comes from the circuit_nets, so it is there. *)
  let rhs_name = PtrHashtbl.find environment ptr in (* And by then the ptr has been given a name. *)
  let expr = match node with
    (* Assumes no dangling pointers  *)
    | CQuestionMark sz -> EQuestionMark sz
    | CNot ptr -> ENot (PtrHashtbl.find environment ptr)
    | CAnd (ptr_1, ptr_2) -> EAnd (PtrHashtbl.find environment ptr_1, PtrHashtbl.find environment ptr_2)
    | COr (ptr_1, ptr_2) -> EOr (PtrHashtbl.find environment ptr_1, PtrHashtbl.find environment ptr_2)
    | CMux (sz, ptr_sel, ptr_t, ptr_f) -> EMux (sz, PtrHashtbl.find environment ptr_sel, PtrHashtbl.find environment ptr_t, PtrHashtbl.find environment ptr_f)
    | CConst l -> EConst (string_of_bits l)
    | CExternal (ffi_sig, ptr_1, ptr_2) -> EExternal (ffi_sig, PtrHashtbl.find environment ptr_1, PtrHashtbl.find environment ptr_2)
    | CReadRegister r_sig -> EReadRegister (r_sig.reg_name)
    | CAnnot (sz, name_rhs, ptr) -> EAnnot (sz, name_rhs, PtrHashtbl.find environment ptr)
  in
  (rhs_name, expr)

let continous_assignments
      (environment: string PtrHashtbl.t)
      (circuit: dedup_result)
    : continous_assignments
  =
    List.map
      (assignment_node
         environment
         (circuit.dedup_ptrs))
      (List.of_seq (PtrHashtbl.to_seq_keys circuit.dedup_ptrs))


(* Phase IV: Update of register *)

type statement = Update of string  * bool list  * string
(* name register, init value, net obtained by looking up the root of the register *)

type statements = statement list


let statements
      (environment: string PtrHashtbl.t)
      (circuit: dedup_result)
    : statements
  =
  assert false
(* Overview of the verilog generation:

 The circuit generation is composed of four sections.
 We describe how to generate the data for each of them, and then we pretty print the data generated.

I Structure
  1- The declaration of inputs and outputs
  2- The declaration of registers and wires
  3- The continuous assignment, defining intermediate nodes
  4- The always block describing what to do with registers on rising edges

II Pretty Printing
  1- io
  2- internals
  3- continous assignments
  4- always blocks
  5- whole module

I Structure
===========

1- io declaration
-----------------

type io =
 | Input of string * nat
 | Output of string * nat

type decl_io = io list

2- Registers and Wires declaration
----------------------------------

 There are two kind of internal objects: wires and registers. The registers are directly created by iteration on the input registers. We assume that the name of the registers are all distincts.

To declare the wires we iterate over the net PtrHash: for each entry in the hashtable we create one wire with the following name and size:
- If the name is given by the value in the hashtable: for a CAnnot or a CExternal, write that name and the size is directly accessible.

- Otherwise there is no name available so we create a freshname: (TODO check if _Wnumber or w_number is better).
All names created that way are added in an environment: ptr -> string

type internal =
 | Reg of string * nat
 | Wire of string * nat

type decl_internal = internal list

3- continous assignment
-----------------------
The net describing the computation of the circuit is representend in the Hashtable.

type expression =
 | Ref string                  (* the String is the name of the node  *)
 | Const string                 (* this string is the string representing the bits to prints for the constants: 3'b000  for example *)
 | Mux string * string * string
 | And string * string
 | Or string  * string
 | Not string * string
 | Select string * string
 | Slice string * string * string
 | ExternalInstance string * string * string * string (* Name instance, arg1, arg2, output *)

For the name of the instance we concatenate the name of the function and the name of the output wire, which
should not collide with any other instance in any reasonable case.

type assignment = (string * expression) (* LHS, RHS *)

type continous_assignments = assignment list

We iterate through the hashtable, for all pointer we generate (name(pointer), compile(pointed))


4- always block
---------------

The update of the register is done in parallel for all the registers: on every rising edge of clock,
if reset then we write the initial value in the register,

type statement =
 | Update string  * (* string register *)
          list bool  * (* init value *)
          string (* net obtained by looking up the root of the register *)

type update = statement list


II Pretty printing
==================

Note: ExternalInstances are instantiated in order.


*)
