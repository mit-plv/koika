open Common
open Cuttlebone
open Cuttlebone.Util
open Cuttlebone.Graphs

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

let io_from_reg (root: circuit_root) : io_decls =
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


let rwcircuit_to_string (rwc: rwcircuit) =
  match rwc with
  | Rwcircuit_rwdata (reg, field) ->
     reg.reg_name ^
       (match field with
        | Rwdata_r0 -> "_read0"
        | Rwdata_r1 -> "_read1"
        | Rwdata_w0 -> "_write0"
        | Rwdata_w1 -> "_write1"
        | Rwdata_data0 -> "_data0"
        | Rwdata_data1 -> "_data1")
  | Rwcircuit_canfire -> "_canfire"

let io_from_bundles (c: circuit) =
  match c.node with
  | CBundle (rule_name, regs) ->
     List.flatten
     @@ List.map (fun (reg,_) ->
                         [ Output("rule_"^rule_name^"_output_"^reg.reg_name^"_data0", typ_sz @@ reg_type reg);
                           Output("rule_"^rule_name^"_output_"^reg.reg_name^"_data1", typ_sz @@ reg_type reg);
                           Output("rule_"^rule_name^"_output_"^reg.reg_name^"_read0", 1);
                           Output("rule_"^rule_name^"_output_"^reg.reg_name^"_read1", 1);
                           Output("rule_"^rule_name^"_output_"^reg.reg_name^"_write0", 1);
                           Output("rule_"^rule_name^"_output_"^reg.reg_name^"_write1", 1) ])
          regs

  | CBundleRef (size, bundle, rwc) ->
     begin
       match bundle.node with
       | CBundle(rule_name, _) ->
          [ Input("rule_"^rule_name^ "_input_" ^ rwcircuit_to_string rwc, size) ]
       | _ -> []
     end
  | _ -> []

let io_declarations (circuit: circuit_graph) : io_decls =
  clock_and_reset @ (List.flatten @@ (List.map io_from_reg (circuit.graph_roots)) @ (List.map io_from_bundles circuit.graph_nodes))


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
 | Nothing

let internal_decl_to_string (internal_decl: internal_decl) =
  match internal_decl with
  | Nothing -> ""
  | Reg (r, sz) ->  if sz <= 1
                     then "\treg " ^ r ^ ";"
                     else "\treg " ^ "[" ^ string_of_int (sz-1) ^ ":0] " ^ r ^ ";"
  | Wire (w, sz) ->  if sz <= 1
                     then "\twire " ^ w ^ ";"
                     else "\twire " ^ "[" ^ string_of_int (sz-1) ^ ":0] " ^ w ^ ";"

type internal_decls = internal_decl list


let internal_decl_for_reg (root: circuit_root) =
  let reg_name = root.root_reg.reg_name in
  let reg_type = reg_type root.root_reg in
  Reg(reg_name, typ_sz reg_type)

let internal_decl_for_net
      (environment: (int, string) Hashtbl.t)
      (gensym : int ref)
      (c: circuit)
  =
  let name_ptr = !gensym in
  gensym := !gensym + 1;
  let name_net = "__inter_" ^ (string_of_int name_ptr) in
  Hashtbl.add environment c.tag name_net;
  match c.node with
  | CNot _
    | CAnd (_, _)
    | COr (_, _) ->   Wire(name_net, 1)
  | CMux (n, _, _, _) -> Wire(name_net, n)
  | CAnnot (n, name , _) ->
     Hashtbl.add environment c.tag (name ^ name_net);
     Wire(name ^ name_net, n) (* Prefix with the name given by the user *)
  | CConst l -> Wire(name_net, Array.length l)
  | CUnop (fn, _) ->
     let fsig = Cuttlebone.Extr.PrimSignatures.coq_Sigma1 (Bits1 fn) in
     Wire(name_net, typ_sz (Cuttlebone.Util.retType fsig))
  | CBinop (fn, _, _) ->
     let fsig = Cuttlebone.Extr.PrimSignatures.coq_Sigma2 (Bits2 fn) in
     Wire(name_net, typ_sz (Cuttlebone.Util.retType fsig))
  | CExternal (ffi_sig, _) -> Wire(name_net, typ_sz ffi_sig.ffi_rettype)
  | CReadRegister r_sig -> Wire(name_net, typ_sz (reg_type r_sig))
  | CBundle (_,_) -> Nothing
  | CBundleRef (sz, _, _) -> Wire(name_net, sz)


let internal_declarations (environment: (int, string) Hashtbl.t) (circuit: circuit_graph) =
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
  | EIO of string
  | EConst of string
  | EUnop of Extr.PrimTyped.fbits1 * string
  | EBinop of Extr.PrimTyped.fbits2 * string * string
  | EExternal of ffi_signature * string
  | EReadRegister of string
  | EAnnot of size_t * string * string

type assignment = string * expression (* LHS, RHS *)

let failwith_unlowered () =
  failwith "The verilog backend doesn't support zextl and zextr: they should be elaborated away by the compiler."

let assignment_to_string (gensym: int ref) (assignment: assignment) =
  let (lhs,expr) = assignment in
  let default_left = "\tassign " ^ lhs ^ " = " in
  (match expr with
   (* | EQuestionMark _ -> default_left ^ "0" (\* TODO check other ways to do  *\) *)
   | ENot n -> default_left ^ "~" ^ n
   | EAnd (arg1, arg2) -> default_left ^ arg1 ^ " & " ^ arg2
   | EOr (arg1, arg2) -> default_left ^ arg1 ^ " | " ^ arg2
   | EMux (_, sel, t, f) -> default_left ^ sel ^ " ? " ^ t ^ " : " ^ f
   | EIO s -> default_left ^ s
   | EConst s -> default_left ^ s
   | EUnop (fn, arg1) ->
      (match fn with
       | Not _ -> default_left ^ "~" ^ arg1
       | Part (_, offset, slice_sz) -> default_left ^ arg1 ^ "[" ^ (string_of_int offset) ^ " +: " ^ string_of_int slice_sz ^ "]"
       | ZExtL _ | ZExtR _ -> failwith_unlowered ())
   | EBinop (fn, arg1, arg2) ->
      (match fn with
       | Plus _ -> default_left ^ arg1 ^ " + " ^ arg2
       | Minus _ -> default_left ^ arg1 ^ " - " ^ arg2
       | Compare (signed, cmp, _sz) ->
          let cast = Printf.sprintf (if signed then "$signed(%s)" else "%s") in
          let op = match cmp with CLt -> "<" | CGt -> ">" | CLe -> "<=" | CGe -> ">=" in
          Printf.sprintf "%s %s %s" (cast arg1) op (cast arg2)
       | Sel _ -> default_left ^ arg1 ^ "[" ^ arg2 ^ "]"
       | PartSubst (sz, offset, slice_sz) ->
          if (offset > 0) then
            if (offset + slice_sz <= sz-1) then
              Printf.sprintf "\tassign %s = {%s[%d : %d], %s, %s[%d : %d]}"
                lhs arg1 (sz-1) (offset+slice_sz)  arg2 arg1 (offset-1) 0
            else
              Printf.sprintf "\tassign %s = { %s, %s[%d : %d]}"
                lhs arg2 arg1 (offset-1) 0
          else
            if sz = 0 then
              failwith "Unhandled case, slicing size 0?"
            else
              Printf.sprintf "assign %s = {%s[%d : %d], %s}"
                lhs arg1 (sz-1) (slice_sz)  arg2
       | IndexedPart (_, slice_sz) -> default_left ^ arg1 ^ "[" ^ arg2 ^ " +: " ^ string_of_int slice_sz ^ "]"
       | And _ ->  default_left ^ arg1 ^ " & " ^ arg2
       | Or _ -> default_left ^ arg1 ^ " | " ^ arg2
       | Xor _ -> default_left ^ arg1 ^ " ^ " ^ arg2
       | Lsl (_, _) -> default_left ^ arg1 ^ " << " ^ arg2
       | Lsr (_, _) -> default_left ^ arg1 ^ " >> " ^ arg2
       | EqBits _ -> default_left ^ arg1 ^ " == " ^ arg2
       | Concat (_, _) -> default_left ^ "{" ^ arg1 ^ ", " ^ arg2 ^ "}")
   | EExternal (ffi, arg) ->
      let number_s = !gensym in (* FIXME use the gensym from common.ml *)
      gensym := !gensym + 1 ;
      "\t"^ ffi.ffi_name ^ " " ^ (ffi.ffi_name ^ "__instance__" ^ string_of_int number_s) ^
        "(" ^ arg ^ "," ^ lhs ^ ")"
   | EReadRegister r -> default_left ^ r
   | EAnnot (_, _, rhs) -> default_left ^ rhs) ^ ";"



type continous_assignments = assignment list

let assignment_node
      (environment: (int, string) Hashtbl.t)
      (c: circuit)
  : continous_assignments
  =
  let env = Hashtbl.find environment in
  let node = c.node in
  match node with
  | CBundleRef (_, bundle , rwc) ->
     begin
       match bundle.node with
       | CBundle (rule_name, _) ->
          [(env c.tag, EIO("rule_"^rule_name^ "_input_" ^ rwcircuit_to_string rwc))]
       | _ -> assert false
     end
  | CBundle (rule_name, list_assigns) ->
     List.flatten
     @@ List.map (fun (reg,rwdata) ->
            [("rule_"^rule_name^"_output_"^reg.reg_name^"_data0", EIO(env rwdata.data0.tag));
             ("rule_"^rule_name^"_output_"^reg.reg_name^"_data1", EIO(env rwdata.data1.tag));
             ("rule_"^rule_name^"_output_"^reg.reg_name^"_read0", EIO(env rwdata.read0.tag));
             ("rule_"^rule_name^"_output_"^reg.reg_name^"_read1", EIO(env rwdata.read1.tag));
             ("rule_"^rule_name^"_output_"^reg.reg_name^"_write0", EIO(env rwdata.write0.tag));
             ("rule_"^rule_name^"_output_"^reg.reg_name^"_write1", EIO(env rwdata.write1.tag))])
          list_assigns
  | _ ->
     begin
     let rhs_name = env c.tag in (* And by then the ptr has been given a name. *)
     let expr = match node with
       (* Assumes no dangling pointers  *)
       | CNot c -> ENot (env c.tag)
       | CAnd (c_1, c_2) -> EAnd (env c_1.tag, env c_2.tag)
       | COr (c_1, c_2) -> EOr (env c_1.tag, env c_2.tag)
       | CMux (sz, c_sel, c_t, c_f) -> EMux (sz,
                                             env c_sel.tag,
                                             env c_t.tag,
                                             env c_f.tag)
       | CConst l -> EConst (string_of_bits l) (* TODO *)
       | CUnop (fn, c_1) -> EUnop (fn, env c_1.tag)
       | CBinop (fn, c_1, c_2) -> EBinop (fn, env c_1.tag, env c_2.tag)
       | CExternal (ffi_sig, c_1) -> EExternal (ffi_sig, env c_1.tag)
       | CReadRegister r_sig -> EReadRegister (r_sig.reg_name)
       | CAnnot (sz, name_rhs, c) -> EAnnot (sz, name_rhs, env c.tag)
       | _ -> assert false
     in
     [(rhs_name, expr)]
     end

let continous_assignments
      (environment: (int, string) Hashtbl.t)
      (circuit: circuit_graph)
    : continous_assignments
  =
  (List.map (fun root -> (root.root_reg.reg_name ^ "__data", EReadRegister root.root_reg.reg_name))
     (circuit.graph_roots)) (* Add output peek into registers *)
    @ List.flatten @@ List.map
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

let statement_to_string ?(add_overwrite_finegrain=false) (statement: statement) =
  let Update (reg, initvalue, net_update) = statement in (* Really we can do that? That's cool *)
  (* So we should compensate with something less cool: *)
  if add_overwrite_finegrain then
  "\talways @(posedge clock) begin\n\t\tif (reset) begin\n\t\t\t" ^ reg ^ " <= " ^ initvalue ^ ";\n" ^
    "\t\tend else begin\n" ^ "\t\t\tif (" ^ reg ^ "__overwrite" ^ ") begin\n" ^
      "\t\t\t\t" ^ reg ^ " <= " ^ reg ^ "__overwrite_data" ^ ";\n\t\t\tend else begin\n" ^
        "\t\t\t\t" ^ reg ^ " <= " ^ net_update ^ ";\n\t\t\tend\n\t\tend\n\tend"
  else
    "\talways @(posedge clock) begin\n\t\tif (reset) begin\n\t\t\t" ^ reg ^ " <= " ^ reg ^ "__overwrite_data" ^ ";\n" ^
    "\t\tend else begin\n" ^
        "\t\t\t\t" ^ reg ^ " <= " ^ net_update ^ ";\n\t\t\tend\n\t\tend\n"

type statements = statement list


let statements
      (environment: (int, string) Hashtbl.t)
      (circuit: circuit_graph)
    : statements
  =
  List.map (fun root ->
      let reg_name = root.root_reg.reg_name in
      let reg_init = string_of_bits (Cuttlebone.Util.bits_of_value root.root_reg.reg_init) in
      let reg_wire_update = Hashtbl.find environment root.root_circuit.tag in
      Update (reg_name, reg_init, reg_wire_update))
    (circuit.graph_roots)

let main out (circuit: circuit_graph) =
  let environment = Hashtbl.create 50 in
  let instance_external_gensym = ref 0 in
  let io_decls = io_declarations circuit in
  let internal_decls = internal_declarations environment circuit in
  let continous_assignments = continous_assignments environment circuit in
  let string_io_decls = (List.map io_decl_to_string io_decls) in
  let statements = statements environment circuit in
  let string_prologue = "module CompilerTest(" ^ (String.concat ",\n\t" string_io_decls) ^ ");" in (* TODO pass a name here *)
  let string_internal_decls = String.concat "\n" (List.map internal_decl_to_string internal_decls) in
  let string_continous_assignments = String.concat "\n" (List.map (assignment_to_string instance_external_gensym)  continous_assignments) in
  let string_statements = String.concat "\n" (List.map statement_to_string statements) in
  let string_epilogue = "endmodule" in
  output_string out (String.concat "\n" [string_prologue; string_internal_decls; string_continous_assignments; string_statements; string_epilogue])
