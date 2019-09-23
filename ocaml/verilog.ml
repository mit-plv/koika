open Common
open SGALib
open SGALib.Util
open SGALib.Graphs

(* TODO: What to do with bit 0?
 *)

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

let io_from_reg (root: _ circuit_root) : io_decls =
  let reg_name = root.root_reg.reg_name in
  let reg_type = reg_type root.root_reg in
  [
    Input (reg_name ^ "__overwrite_data", typ_sz reg_type);
    Input (reg_name ^ "__overwrite", 1);
    Output (reg_name ^ "__data", typ_sz reg_type)
  ]
let clock_and_reset : io_decls =
  [
    Input ("clock", 1);
    Input ("reset", 1);
  ]

let io_declarations (circuit: _ circuit_graph) : io_decls =
  clock_and_reset @ List.flatten (List.map io_from_reg (circuit.graph_roots))


(* Phase II: Internal declarations


   We declare the internal registers, and one wire per subcircuit i.e
   one per nodes of (circuit_nets: circuit Hashtbl.t).  The signal
   are all named __inter_n except for the one where a name has been
   given by the user; then we name them givenname__inter_n. The sizes
   of registers and internal wires are also declared in that phase.

 *)
type internal_decl =
 | Reg of string * int
 | Wire of string * int

let internal_decl_to_string (internal_decl: internal_decl) =
  match internal_decl with
  | Reg (r, sz) ->  if sz <= 1
                     then "\treg " ^ r ^ ";"
                     else "\treg " ^ "[" ^ string_of_int (sz-1) ^ ":0] " ^ r ^ ";"
  | Wire (w, sz) ->  if sz <= 1
                     then "\twire " ^ w ^ ";"
                     else "\twire " ^ "[" ^ string_of_int (sz-1) ^ ":0] " ^ w ^ ";"

type internal_decls = internal_decl list


let internal_decl_for_reg (root: _ circuit_root) =
  let reg_name = root.root_reg.reg_name in
  let reg_type = reg_type root.root_reg in
  Reg(reg_name, typ_sz reg_type)

let internal_decl_for_net
      (environment: (int, string) Hashtbl.t)
      (gensym : int ref)
      (c: _ circuit)
  =
  let name_ptr = !gensym in
  gensym := !gensym + 1;
  let name_net = "__inter_" ^ (string_of_int name_ptr) in
  Hashtbl.add environment c.tag name_net;
  match c.node with
  | CNot _
    | CAnd (_, _)
    | COr (_, _) ->   Wire(name_net, 1)
  (* | CQuestionMark n *)
  | CMux (n, _, _, _) -> Wire(name_net, n)
  | CAnnot (n, name , _) ->
     Hashtbl.add environment c.tag (name ^ name_net);
     Wire(name ^ name_net, n) (* Prefix with the name given by the user *)
  | CConst l -> Wire(name_net, Array.length l)
  | CExternal (ffi_sig, _, _) -> Wire(name_net, typ_sz ffi_sig.ffi_rettype)
  | CReadRegister r_sig -> Wire(name_net, typ_sz (reg_type r_sig))

let internal_declarations (environment: (int, string) Hashtbl.t) (circuit: _ circuit_graph) =
  let gensym = ref 0 in
  let reg_declarations = List.map internal_decl_for_reg (circuit.graph_roots) in
  let internal_declarations = List.map
                                (internal_decl_for_net
                                   environment
                                   gensym)
                                circuit.graph_nodes
  in
  reg_declarations @ internal_declarations


(* Phase III: Continuous assignments

   Every node in the netlist (circuit_nets: circuit Hashtbl.t)
   corresponds to one verilog assign statement that is declaring how
   the left hand side wire gets computed from registers and wires.

   We also assign the output wires to peek in the registers

   For custom functions we create an instance of the module in verilog
   for each such CustomFn encountered.

 *)
type expression =
  (* | EQuestionMark of size_t *)
  | ENot of string
  | EAnd of string * string
  | EOr of string * string
  | EMux of size_t * string * string * string
  | EConst of string
  | EExternal of (SGA.prim_fn_t, string) fun_id_t ffi_signature * string * string
  | EReadRegister of string
  | EAnnot of size_t * string * string

type assignment = string * expression (* LHS, RHS *)

let assignment_to_string (gensym: int ref) (assignment: assignment) =
  let (lhs,expr) = assignment in
  let default_left = "\tassign " ^ lhs ^ " = " in
  (match expr with
   (* | EQuestionMark _ -> default_left ^ "0" (\* TODO check other ways to do  *\) *)
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
                       "\t"^ s ^ " " ^ (s ^ "__instance__" ^ string_of_int number_s) ^
                         "(" ^ arg1 ^ ", " ^ arg2 ^ "," ^ lhs ^ ")"
       | PrimFn (BitsFn typePrim) ->
          (match typePrim with
           | SGA.UIntPlus _ -> default_left ^ arg1 ^ " + " ^ arg2
           | SGA.Sel _ -> default_left ^ arg1 ^ "[" ^ arg2 ^ "]"
           | SGA.Part (_, offset, slice_sz) -> default_left ^ arg1 ^ "[" ^ (string_of_int offset) ^ " +: " ^ string_of_int slice_sz ^ "]"
           | SGA.PartSubst (_, offset, slice_sz) ->
              Printf.sprintf "assign %s = %s; assign %s[%d +: %d] = %s; // FIXME"
                lhs arg1 lhs offset slice_sz arg2
           | SGA.IndexedPart (_, slice_sz) -> default_left ^ arg1 ^ "[" ^ arg2 ^ " +: " ^ string_of_int slice_sz ^ "]"
           | SGA.And _ ->  default_left ^ arg1 ^ " & " ^ arg2
           | SGA.Or _ -> default_left ^ arg1 ^ " | " ^ arg2
           | SGA.Not _ -> default_left ^ "~" ^ arg1
           | SGA.Lsl (_, _) -> default_left ^ arg1 ^ " << " ^ arg2
           | SGA.Lsr (_, _) -> default_left ^ arg1 ^ " >> " ^ arg2
           | SGA.Eq _ -> default_left ^ arg1 ^ " == " ^ arg2
           | SGA.Concat (_, _) -> default_left ^ "{" ^ arg1 ^ ", " ^ arg2 ^ "}"
           | SGA.ZExtL (_, _) -> failwith "TODO UNIMPLEMENTED ZEXTL" (* TODO: convince clement that those are not needed as primitive *)
           | SGA.ZExtR (_, _) -> failwith "TODO UNIMPLEMENTED ZEXTR" (* TODO: convince clement that those are not needed as primitive *)
          )
       | PrimFn (SGA.ConvFn _)
       | PrimFn (SGA.StructFn _) ->
          failwith "The verilog backend doesn't support enum and structs.
Make sure to pass elaborate_externals_1 to compile_scheduler."
      )
   | EReadRegister r -> default_left ^ r
   | EAnnot (_, _, rhs) -> default_left ^ rhs) ^ ";"



type continous_assignments = assignment list


let assignment_node
      (environment: (int, string) Hashtbl.t)
      (c: _ circuit)
  : assignment
  =
  let node = c.node in
  let rhs_name = Hashtbl.find environment c.tag in (* And by then the ptr has been given a name. *)
  let expr = match node with
    (* Assumes no dangling pointers  *)
    (* | CQuestionMark sz -> EQuestionMark sz *)
    | CNot c -> ENot (Hashtbl.find environment c.tag)
    | CAnd (c_1, c_2) -> EAnd (Hashtbl.find environment c_1.tag, Hashtbl.find environment c_2.tag)
    | COr (c_1, c_2) -> EOr (Hashtbl.find environment c_1.tag, Hashtbl.find environment c_2.tag)
    | CMux (sz, c_sel, c_t, c_f) -> EMux (sz, Hashtbl.find environment c_sel.tag, Hashtbl.find environment c_t.tag, Hashtbl.find environment c_f.tag)
    | CConst l -> EConst (string_of_bits l) (* TODO *)
    | CExternal (ffi_sig, c_1, c_2) -> EExternal (ffi_sig, Hashtbl.find environment c_1.tag, Hashtbl.find environment c_2.tag)
    | CReadRegister r_sig -> EReadRegister (r_sig.reg_name)
    | CAnnot (sz, name_rhs, c) -> EAnnot (sz, name_rhs, Hashtbl.find environment c.tag)
  in
  (rhs_name, expr)

let continous_assignments
      (environment: (int, string) Hashtbl.t)
      (circuit: _ circuit_graph)
    : continous_assignments
  =
  (List.map (fun root -> (root.root_reg.reg_name ^ "__data", EReadRegister root.root_reg.reg_name))
     (circuit.graph_roots)) (* Add output peek into registers *)
    @ List.map
      (assignment_node
         environment)
      circuit.graph_nodes


(* Phase IV: Update of register


   The update of the registers are done in parallel for all the
   registers: on every rising edge of clock, if reset is high then we
   write the initial value of the register, otherwise if overwrite is
   high, we write the value coming from the environment, otherwise we
   write the value computed by the root wire of that register.

 *)

type statement = Update of string  * string  * string
(* name register, init value, net obtained by looking up the root of the register *)

let statement_to_string (statement: statement) =
  let Update (reg, initvalue, net_update) = statement in (* Really we can do that? That's cool *)
  (* So we should compensate with something less cool: *)
  "\talways @(posedge clock) begin\n\t\tif (reset) begin\n\t\t\t" ^ reg ^ " <= " ^ initvalue ^ ";\n" ^
    "\t\tend else begin\n" ^ "\t\t\tif (" ^ reg ^ "__overwrite" ^ ") begin\n" ^
      "\t\t\t\t" ^ reg ^ " <= " ^ reg ^ "__overwrite_data" ^ ";\n\t\t\tend else begin\n" ^
        "\t\t\t\t" ^ reg ^ " <= " ^ net_update ^ ";\n\t\t\tend\n\t\tend\n\tend"

type statements = statement list


let statements
      (environment: (int, string) Hashtbl.t)
      (circuit: _ circuit_graph)
    : statements
  =
  List.map (fun root ->
      let reg_name = root.root_reg.reg_name in
      let reg_init = string_of_bits (SGALib.Util.bits_of_value root.root_reg.reg_init) in
      let reg_wire_update = Hashtbl.find environment root.root_circuit.tag in
      Update (reg_name, reg_init, reg_wire_update))
    (circuit.graph_roots)

let main out (circuit: (SGALib.SGA.prim_fn_t, _) circuit_graph) =
  let environment = Hashtbl.create 50 in
  let instance_external_gensym = ref 0 in
  let io_decls = io_declarations circuit in
  let internal_decls = internal_declarations environment circuit in
  let continous_assignments = continous_assignments environment circuit in
  let string_io_decls = List.map io_decl_to_string io_decls in
  let statements = statements environment circuit in
  let string_prologue = "module CompilerTest(" ^ (String.concat ", " string_io_decls) ^ ");" in (* TODO pass a name here *)
  let string_internal_decls = String.concat "\n" (List.map internal_decl_to_string internal_decls) in
  let string_continous_assignments = String.concat "\n" (List.map (assignment_to_string instance_external_gensym)  continous_assignments) in
  let string_statements = String.concat "\n" (List.map statement_to_string statements) in
  let string_epilogue = "endmodule" in
  output_string out (String.concat "\n" [string_prologue; string_internal_decls; string_continous_assignments; string_statements; string_epilogue])
