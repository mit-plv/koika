(*! OCaml wrappers around functionality provided by the library extracted from Coq !*)
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

open Common
module Extr = Extr

type ('name_t, 'reg_t, 'ext_fn_t) extr_circuit =
  ('name_t, 'reg_t, 'ext_fn_t, ('name_t, 'reg_t, 'ext_fn_t) Extr.rwdata) Extr.circuit

(* FIXME: expose these options on the command line *)
let strip_annotations = false
let hashcons_circuits = false

type extr_type = Extr.type0

module Util = struct
  let log2 =
    Extr.Nat.log2_up

  let list_nth (l: 'a list) (n: Extr.index) =
    Extr.list_nth l n

  let string_of_coq_string chars =
    String.concat "" (List.map (String.make 1) chars)

  let coq_string_of_string s =
    List.of_seq (String.to_seq s)

  let array_of_vect sz bs =
    Array.of_list (Extr.vect_to_list sz bs)

  let vect_of_array (bs: 'a array) =
    Extr.vect_of_list (Array.to_list bs)

  let rec typ_of_extr_type (tau: extr_type) : typ =
    match tau with
    | Extr.Bits_t sz -> Bits_t sz
    | Extr.Enum_t sg -> Enum_t (enum_sig_of_extr_enum_sig sg)
    | Extr.Struct_t sg -> Struct_t (struct_sig_of_extr_struct_sig sg)
    | Extr.Array_t sg -> Array_t (array_sig_of_extr_array_sig sg)
  and struct_sig_of_extr_struct_sig { struct_name; struct_fields } : struct_sig =
    { struct_name = string_of_coq_string struct_name;
      struct_fields = List.map (fun (nm, tau) ->
                          (string_of_coq_string nm, typ_of_extr_type tau))
                        struct_fields }
  and enum_sig_of_extr_enum_sig { enum_name; enum_size; enum_bitsize; enum_members; enum_bitpatterns } : enum_sig =
    { enum_name = string_of_coq_string enum_name;
      enum_bitsize;
      enum_members =
        List.map (fun (nm, bs) ->
            (string_of_coq_string nm, array_of_vect enum_bitsize bs))
          (Extr.vect_to_list enum_size (Extr.vect_zip enum_size enum_members enum_bitpatterns)) }
  and array_sig_of_extr_array_sig { array_type; array_len } =
    { array_type = typ_of_extr_type array_type; array_len }

  let rec extr_type_of_typ (tau: typ) : extr_type =
    match tau with
    | Bits_t sz -> Extr.Bits_t sz
    | Enum_t sg -> Extr.Enum_t (extr_enum_sig_of_enum_sig sg)
    | Struct_t sg -> Extr.Struct_t (extr_struct_sig_of_struct_sig sg)
    | Array_t sg -> Extr.Array_t (extr_array_sig_of_array_sig sg)
  and extr_struct_sig_of_struct_sig { struct_name; struct_fields } : extr_type Extr.struct_sig' =
    { struct_name = coq_string_of_string struct_name;
      struct_fields = List.map (fun (nm, tau) ->
                          (coq_string_of_string nm, extr_type_of_typ tau))
                        struct_fields }
  and extr_enum_sig_of_enum_sig { enum_name; enum_bitsize; enum_members } : Extr.enum_sig =
    { enum_name = coq_string_of_string enum_name;
      enum_bitsize;
      enum_size = List.length enum_members;
      enum_members = Extr.vect_of_list (List.map (fun (nm, _) -> coq_string_of_string nm) enum_members);
      enum_bitpatterns = Extr.vect_of_list (List.map (fun (_, bs) -> vect_of_array bs) enum_members) }
  and extr_array_sig_of_array_sig { array_type; array_len } =
    { array_type = extr_type_of_typ array_type;
      array_len = array_len }

  type extr_sig = Extr.type0 Extr._Sig

  let argType nargs (fsig: extr_sig) idx : typ =
    typ_of_extr_type @@ List.nth (Extr.vect_to_list nargs fsig.argSigs) idx

  let retSig (fsig: extr_sig) : typ =
    typ_of_extr_type fsig.retSig

  let ffi_sig_of_extr_external_sig ffi_name fsig =
    Extr.{ ffi_name;
           ffi_argtype = argType 1 fsig 0;
           ffi_rettype = typ_of_extr_type fsig.retSig }

  let extr_external_sig_of_ffi_sig { ffi_argtype; ffi_rettype; _ } =
    Extr.{ argSigs = Extr.vect_of_list [extr_type_of_typ ffi_argtype];
          retSig = extr_type_of_typ ffi_rettype }

  let extr_intfun_of_intfun fbody (fsig: _ Common.internal_function) =
    { Extr.int_name = fsig.int_name;
      Extr.int_argspec = List.map (fun (nm, tau) -> nm, extr_type_of_typ tau) fsig.int_argspec;
      Extr.int_retSig = extr_type_of_typ fsig.int_retSig;
      Extr.int_body = fbody fsig.int_body }

  let intfun_of_extr_intfun fbody (fsig: _ Extr.internalFunction) =
    { int_name = fsig.int_name;
      int_argspec = List.map (fun (nm, tau) -> nm, typ_of_extr_type tau) fsig.int_argspec;
      int_retSig = typ_of_extr_type fsig.int_retSig;
      int_body = fbody fsig.int_body }

  let extr_type_to_string tau =
    typ_to_string (typ_of_extr_type tau)

  let extr_enum_sig_to_string sg =
    enum_sig_to_string (enum_sig_of_extr_enum_sig sg)

  let extr_struct_sig_to_string sg =
    struct_sig_to_string (struct_sig_of_extr_struct_sig sg)

  let extr_array_sig_to_string sg =
    array_sig_to_string (array_sig_of_extr_array_sig sg)

  let type_kind_to_string (tk: Extr.type_kind) =
    match tk with
    | Extr.Kind_bits -> "bits"
    | Extr.Kind_enum None -> "enum"
    | Extr.Kind_enum (Some sg) -> extr_enum_sig_to_string sg
    | Extr.Kind_struct None -> "struct"
    | Extr.Kind_struct (Some sg) -> extr_struct_sig_to_string sg
    | Extr.Kind_array None -> "array"
    | Extr.Kind_array (Some sg) -> extr_array_sig_to_string sg

  let string_eq_dec =
    { Extr.eq_dec = fun (s1: string) (s2: string) -> s1 = s2 }

  let any_eq_dec =
    { Extr.eq_dec = fun (s1: 'a) (s2: 'a) -> s1 = s2 }

  let string_show =
    { Extr.show0 = coq_string_of_string }

  type 'var_t extr_error_message =
    | ExplicitErrorInAst
    | SugaredConstructorInAst
    | UnboundVariable of { var: 'var_t }
    | OutOfBounds of { pos: int; sg: array_sig }
    | UnboundField of { field: string; sg: struct_sig }
    | UnboundEnumMember of { name: string; sg: enum_sig }
    | TooManyArguments of { name: string; actual: int; expected: int }
    | TooFewArguments of { name: string; actual: int; expected: int }
    | TypeMismatch of { expected: typ; actual: typ }
    | KindMismatch of { actual: string; expected: string }

  let translate_extr_error_message = function
    | Extr.ExplicitErrorInAst ->
       ExplicitErrorInAst
    | Extr.SugaredConstructorInAst ->
       SugaredConstructorInAst
    | Extr.UnboundVariable var ->
       UnboundVariable { var }
    | Extr.UnboundEnumMember (name, sg) ->
       UnboundEnumMember { name = string_of_coq_string name;
                           sg = enum_sig_of_extr_enum_sig sg }
    | Extr.TooManyArguments (name, expected, nextras) ->
       TooManyArguments { name; expected; actual = expected + nextras }
    | Extr.TooFewArguments (name, expected, nmissing) ->
       TooFewArguments { name; expected; actual = expected - nmissing }
    |Extr.BasicError err ->
      match err with
      | Extr.OutOfBounds (pos, sg) ->
         OutOfBounds { pos; sg = array_sig_of_extr_array_sig sg }
      | Extr.UnboundField (field, sg) ->
         UnboundField { field = string_of_coq_string field;
                        sg = struct_sig_of_extr_struct_sig sg }
      | Extr.TypeMismatch (actual, expected) ->
         TypeMismatch { actual = typ_of_extr_type actual;
                        expected = typ_of_extr_type expected }
      | Extr.KindMismatch (actual, expected) ->
         KindMismatch { actual = type_kind_to_string actual;
                        expected = type_kind_to_string expected }

  let rec value_of_extr_value tau (v: Extr.type_denote) =
    match tau with
    | Extr.Bits_t sz ->
       Bits (array_of_vect sz v)
    | Extr.Enum_t sg ->
       Enum (enum_sig_of_extr_enum_sig sg, array_of_vect sg.enum_bitsize v)
    | Extr.Struct_t sg ->
       Struct (struct_sig_of_extr_struct_sig sg,
               List.map snd (Extr.struct_to_list value_of_extr_value sg.struct_fields v))
    | Extr.Array_t sg ->
       let extr_values = array_of_vect sg.array_len v in
       let values = Array.map (value_of_extr_value sg.array_type) extr_values in
       Array (array_sig_of_extr_array_sig sg, values)

  let rec extr_value_of_value (v: value) : Extr.type0 * Extr.type_denote =
    match v with
    | Bits bs -> Extr.Bits_t (Array.length bs), (vect_of_array bs)
    | Enum (sg, v) -> Extr.Enum_t (extr_enum_sig_of_enum_sig sg), (vect_of_array v)
    | Struct (sg, sv) ->
       let vv =
         List.map2 (fun (nm, _) v -> coq_string_of_string nm, v)
           sg.struct_fields sv in
       let conv v =
         let tau, extr_v = extr_value_of_value v in
         Extr.ExistT (tau, extr_v) in
       (Extr.Struct_t (extr_struct_sig_of_struct_sig sg),
        Extr.struct_of_list conv vv)
    | Array (sg, values) ->
       (Extr.Array_t (extr_array_sig_of_array_sig sg),
        vect_of_array (Array.map (fun v -> snd (extr_value_of_value v)) values))

  let bits_of_value (v: value) : bool array =
    let tau, v = extr_value_of_value v in
    array_of_vect (Extr.type_sz tau) (Extr.bits_of_value tau v)

  let rec string_of_value (v: value) =
    match v with
    | Bits bs -> string_of_bits bs
    | Enum (sg, v) -> string_of_enum sg v
    | Struct (sg, v) -> string_of_struct sg v
    | Array (_, v) -> string_of_array v
  and string_of_bits (bs: bits_value) =
    let sbit b =
      if b then "1" else "0" in
    let zerop bs =
      Array.for_all (fun b -> b = false) bs in
    let bitstring =
      if zerop bs then "0"
      else let bits = List.rev_map sbit (Array.to_list bs) in
           String.concat "" bits in
    Printf.sprintf "%d'b%s" (Array.length bs) bitstring
  and string_of_enum sg bs =
    sg.enum_name ^
      match List.find_opt (fun (_nm, bs') -> bs' = bs) sg.enum_members with
      | Some (nm, _) -> "::" ^ nm
      | None -> Printf.sprintf "{%s}" (string_of_bits bs)
  and string_of_struct sg v =
    let sp_field ((nm, _tau), v) =
      Printf.sprintf "%s = %s" nm (string_of_value v) in
    Printf.sprintf "%s { %s }" sg.struct_name
      (String.concat ", " (List.map sp_field (List.combine sg.struct_fields v)))
  and string_of_array v =
    let strs = List.map string_of_value (Array.to_list v) in
    Printf.sprintf "[|%s|]" (String.concat "; " strs)

  let reg_sigs_of_koika_package (pkg: _ Extr.koika_package_t) r =
    let reg_init =
      value_of_extr_value (pkg.koika_reg_types r) (pkg.koika_reg_init r) in
    { reg_name = string_of_coq_string (pkg.koika_reg_names.show0 r);
      reg_init }

  let interp_arithmetic a =
    match Extr.action_type a, Extr.interp_arithmetic a with
    | Some tau, Some v -> Some (value_of_extr_value tau v)
    | _, _ -> None

  let finiteType_of_list elements =
    let reg_indices = List.mapi (fun i x -> x, i) elements in
    (* Reverse so that deduplication removes high indices *)
    let regmap = Hashtbl.of_seq (List.to_seq (List.rev reg_indices)) in
    { Extr.finite_elements = elements;
      Extr.finite_index = fun r -> Hashtbl.find regmap r }

  let contextEnv registers =
    Extr.contextEnv (finiteType_of_list registers)

  let dedup (l: 'a list) =
    List.to_seq l |> Seq.map (fun x -> (x, ()))
    |> Hashtbl.of_seq |> Hashtbl.to_seq_keys |> List.of_seq

  let compute_register_histories (type reg_t fn_name_t rule_name_t)
        (_R: reg_t -> extr_type)
        (registers: reg_t list)
        (rule_names: rule_name_t list)
        (rules: rule_name_t -> ('pos_t, 'var_t, fn_name_t, reg_t, 'ext_fn_t) Extr.rule)
        (scheduler: ('pos_t, rule_name_t) Extr.scheduler)
      : (rule_name_t -> reg_t -> Extr.register_history)
        * (rule_name_t -> ('pos_t, 'var_t, fn_name_t, reg_t, 'fn_t) Extr.annotated_rule)
        * (reg_t -> Extr.register_kind) =
    (* Taking in a list of rules allows us to ensure that we annotate all rules,
       not just those mentioned in the scheduler. *)
    (* FIXME: this works only for linear schedulers *)
    let rEnv = contextEnv registers in
    let rlEnv = contextEnv rule_names in
    let (reg_histories, annotated_rules), classified_registers =
      Extr.compute_register_histories _R rEnv rlEnv rules scheduler in
    ((fun (rl: rule_name_t) (r: reg_t) -> Extr.getenv rEnv (Extr.getenv rlEnv reg_histories rl) r),
     (fun (rl: rule_name_t) -> Extr.getenv rlEnv annotated_rules rl),
     (fun (r: reg_t) -> Extr.getenv rEnv classified_registers r))

  let may_fail_without_revert registers histories =
    Extr.may_fail_without_revert (contextEnv registers) histories

  let unop_to_str =
    let open Extr.PrimTyped in
    function
    | Not _ -> "not"
    | SExt (_, _) -> "sext"
    | ZExtL (_, _) -> "zextl"
    | ZExtR (_, _) -> "zextr"
    | Repeat (_, _) -> "repeat"
    | Slice (_, _, _) -> "slice"
    | Lowered _ -> "lowered"

  let binop_to_str =
    let open Extr.PrimTyped in
    function
    | Mul _ -> "mul"
    | And _ -> "and"
    | Or _ -> "or"
    | Xor _ -> "xor"
    | Lsl (_, _) -> "lsl"
    | Lsr (_, _) -> "lsr"
    | Asr (_, _) -> "asr"
    | Concat (_, _) -> "concat"
    | Sel _ -> "sel"
    | SliceSubst (_, _, _) -> "slicesubst"
    | IndexedSlice (_, _) -> "indexedslice"
    | Plus _ -> "plus"
    | Minus _ -> "minus"
    | EqBits (_, _) -> "eqbits"
    | Compare (_, _, _) -> "compare"
end

module Compilation = struct
  let translate_port = function
    | P0 -> Extr.P0
    | P1 -> Extr.P1

  type 'f extr_uaction =
    ('f, var_t, fn_name_t, reg_signature, ffi_signature) Extr.uaction
  type 'f extr_scheduler =
    ('f, rule_name_t) Extr.scheduler

  type 'f extr_action = ('f, var_t, fn_name_t, reg_signature, ffi_signature) Extr.action
  type 'f extr_rule = [ `ExternalRule | `InternalRule ] * 'f extr_action

  let _R = fun rs -> Util.extr_type_of_typ (reg_type rs)
  let _Sigma fn = Util.extr_external_sig_of_ffi_sig fn

  (* FIXME hashmaps, not lists *)
  type 'f compile_unit =
    { c_modname: string;
      c_registers: reg_signature list;
      c_scheduler: ('f, string) Extr.scheduler;
      c_rules: (rule_name_t * 'f extr_rule) list;
      c_cpp_preamble: string option;
      c_pos_of_pos: 'f -> Pos.t }

  type compiled_circuit =
    (string, reg_signature, ffi_signature) extr_circuit

  let result_of_type_result = function
    | Extr.Success s -> Ok s
    | Extr.Failure (err: _ Extr.error) -> Error (err.epos, Util.translate_extr_error_message err.emsg)

  let typecheck_rule pos (ast: 'f extr_uaction) : ('f extr_action, ('f * _)) result =
    let desugared = Extr.desugar_action pos ast in
    let typed = Extr.tc_rule Util.string_eq_dec _R _Sigma pos desugared in
    result_of_type_result typed

  let rec extr_circuit_equivb sz max_depth (c1: _ extr_circuit) (c2: _ extr_circuit) =
    if max_depth < 0 then false
    else
      let eqb = extr_circuit_equivb sz (max_depth - 1) in
      let c1, c2 = Extr.unannot0 sz c1, Extr.unannot0 sz c2 in
      c1 == c2 ||
        match c1, c2 with
        | CMux (_, s1, c11, c12), CMux (_, s2, c21, c22) -> eqb s1 s2 && eqb c11 c21 && eqb c12 c22
        | CConst (sz1, v1), CConst (sz2, v2) -> Util.array_of_vect sz1 v1 = Util.array_of_vect sz2 v2
        | CReadRegister r1, CReadRegister r2 -> r1 == r2
        | CUnop (op1, c1), CUnop (op2, c2) -> op1 == op2 && eqb c1 c2
        | CBinop (op1, c11, c12), CBinop (op2, c21, c22) -> op1 == op2 && eqb c11 c21 && eqb c12 c22
        | CExternal (f1, c1), CExternal (f2, c2) -> f1 == f2 && eqb c1 c2
        | CBundleRef (_, _, _, _, _, _), CBundleRef (_, _, _, _, _, _) -> c1 == c2
        | CAnnot (_, a1, c1), CAnnot (_, a2, c2) -> a1 = a2 && eqb c1 c2
        | _, _ -> false

  let extr_circuit_incomplete_equivb sz c1 c2 =
    (* FIXME: instead of a recursive comparison, we could do the hashconsing as
       an additional optimization pass, which would make pointer-equality
       comparisons complete.  Care should be taken to handle annotations
       correctly, though. *)
    if c1 == c2 then
      true
    else if Hashtbl.hash c1 = Hashtbl.hash c2 then
      extr_circuit_equivb sz max_int c1 c2
    else
      (* This function doesn't need to be complete, but it needs to be sound. *)
      false

  let opt _R _Sigma =
    let open Extr in
    (* let equivb _ c1 c2 = c1 == c2 in *)
    let equivb = extr_circuit_incomplete_equivb in
    let cR, cSigma = lower_R _R, lower_Sigma _Sigma in
    (lco_all_iterated cR cSigma equivb 10).lco_fn

  let compile (cu: 'f compile_unit) : (reg_signature -> compiled_circuit) =
    let finiteType = Util.finiteType_of_list cu.c_registers in
    let rules r = List.assoc r cu.c_rules |> snd in
    let externalp r = (List.assoc r cu.c_rules |> fst) = `ExternalRule in
    let rEnv = Extr.contextEnv finiteType in
    let env = Extr.compile_scheduler _R _Sigma finiteType
                Util.string_show Util.string_show
                (opt _R _Sigma) rules externalp cu.c_scheduler in
    (fun r -> Extr.getenv rEnv env r)
end

module Graphs = struct
  (* Careful with this definition: the hashcons module keeps weak pointers to
     Hashcons.hash_consed record. *)
  type circuit = circuit' Hashcons.hash_consed
  and circuit' =
    | CMux of int * circuit * circuit * circuit
    | CConst of bits_value
    | CReadRegister of reg_signature
    | CUnop of Extr.PrimTyped.fbits1 * circuit
    | CBinop of Extr.PrimTyped.fbits2 * circuit * circuit
    | CExternal of { f: ffi_signature; internal: bool; arg: circuit }
    | CBundle of string * ((reg_signature * rwdata) list)
    | CBundleRef of int * circuit * rwcircuit
    | CAnnot of int * string * circuit
  and rwcircuit =
    | Rwcircuit_rwdata of reg_signature * Extr.rwdata_field
    | Rwcircuit_canfire
  and rwdata =
    { read0 : circuit;
      read1 : circuit;
      write0 : circuit;
      write1 : circuit;
      data0 : circuit;
      data1 : circuit }

  let circuit_to_str =
    let open Printf in
    function
    | CMux (_, s, c1, c2) -> sprintf "CMux (%d, %d, %d)" s.tag c1.tag c2.tag
    | CConst cst -> sprintf "CConst %s" (Util.string_of_bits cst)
    | CReadRegister r -> sprintf "CReadRegister %s" r.reg_name
    | CUnop (f, c) -> sprintf "CUnop (%s, %d)" (Util.unop_to_str f) c.tag
    | CBinop (f, c1, c2) -> sprintf "CBinop (%s, %d, %d)" (Util.binop_to_str f) c1.tag c2.tag
    | CExternal { arg; _ } -> sprintf "CExternal (_, %d)" arg.tag
    | CBundle (_, _) -> sprintf "CBundle"
    | CBundleRef (_, _, _) -> sprintf "CBundleRef"
    | CAnnot (_, a, c) -> sprintf "CAnnot \"%s\" %d" a c.tag

  let rec rwcircuit_of_extr_rwcircuit (reg_sigs: 'a -> reg_signature) = function
    | Extr.Rwcircuit_rwdata (r, field) -> Rwcircuit_rwdata (reg_sigs r, field)
    | Extr.Rwcircuit_canfire -> Rwcircuit_canfire

  type circuit_root = {
      root_reg: reg_signature;
      root_circuit: circuit;
    }

  type circuit_graph = {
      graph_roots: circuit_root list;
      graph_nodes: circuit list
    }

  type ('rule_name_t, 'reg_t, 'ext_fn_t) dedup_input_t = {
      di_regs: 'reg_t list;
      di_reg_sigs: 'reg_t -> reg_signature;
      di_fn_specs: 'ext_fn_t -> (ffi_signature * [`Internal | `External]);
      di_rule_names: 'rule_name_t -> string;
      di_rule_external: 'rule_name_t -> bool;
      di_circuits : 'reg_t -> ('rule_name_t, 'reg_t, 'ext_fn_t) extr_circuit;
      di_strip_annotations: bool;
    }

  module CircuitHash = struct
    type t = circuit'
    let rec equal (c: circuit') (c': circuit') =
      match c, c' with
      | CMux (_, c1, c2, c3), CMux (_, c1', c2', c3') ->
         c1 == c1' && c2 == c2' && c3 == c3'
      | CConst b, CConst b' ->
         b = b' (* Not hashconsed *)
      | CReadRegister r, CReadRegister r' ->
         r = r' (* Not hashconsed *)
      | CUnop (f, a1), CUnop (f', a1') ->
         f = f' (* Not hashconsed *) && a1 == a1'
      | CBinop (f, a1, a2), CBinop (f', a1', a2') ->
         f = f' (* Not hashconsed *) && a1 == a1' && a2 == a2'
      | CExternal c, CExternal c' ->
         c.f = c'.f && c.internal = c'.internal (* Not hashconsed *) && c.arg == c'.arg
      | CBundle (rule_name1, rwset1), CBundle (rule_name2, rwset2) ->
         rule_name1 = rule_name2 && equal_rwsets rwset1 rwset2
      | CBundleRef (_, bundle1, field1 ), CBundleRef (_, bundle2, field2) ->
         bundle1 == bundle2 && field1 = field2
      | CAnnot (_, s, c), CAnnot (_, s', c') ->
         s = s' (* Not hashconsed *) && c == c'
      | _, _ -> false
    and equal_rwsets rwset1 rwset2 =
      List.length rwset1 = List.length rwset2
      && List.for_all2 (fun (rs1, rwdata1) (rs2, rwdata2) ->
            rs1 = rs2 && equal_rwdata rwdata1 rwdata2)
          rwset1 rwset2
    and equal_rwdata rwdata1 rwdata2 =
      rwdata1.read0 == rwdata2.read0
      && rwdata1.read1 == rwdata2.read1
      && rwdata1.write0 == rwdata2.write0
      && rwdata1.write1 == rwdata2.write1
      && rwdata1.data0 == rwdata2.data0
      && rwdata1.data1 == rwdata2.data1

    let h1 x = Hashtbl.hash x
    let h2 h h' = 0x61C8864680B583EB * h + h'
    let h3 h h' h'' = h2 (h2 h h') h''
    let rec hash (c: t) =
      match c with
      | CMux (_, c1, c2, c3) -> 1 + h3 c1.hkey c2.hkey c3.hkey
      | CConst c -> 2 + Hashtbl.hash c
      | CReadRegister { reg_name; _ } -> 3 + h1 reg_name
      | CUnop (f, a1) -> 4 + h2 (h1 f) a1.hkey
      | CBinop (f, a1, a2) -> 5 + h3 (h1 f) a1.hkey a2.hkey
      | CExternal { f; arg; _ } -> 6 + h2 (h1 f) arg.hkey
      | CBundle (rule_name, rwset) -> 7 + h2 (h1 rule_name) (hash_rwset rwset)
      | CBundleRef (_, bundle, field) -> 8 + h2 bundle.hkey (h1 field)
      | CAnnot (_, s, c) -> 9 + h2 (h1 s) c.hkey
    and hash_rwset r =
      Hashtbl.hash (List.map (fun (_, rwd) -> hash_rwdata rwd) r)
    and hash_rwdata rwd =
      h3 (h2 rwd.read0.hkey rwd.read1.hkey)
        (h2 rwd.write0.hkey rwd.write1.hkey)
        (h2 rwd.data0.hkey rwd.data1.hkey)
  end

  module CircuitPhysicalHash = struct
    type t = circuit'
    let equal (c: circuit') (c': circuit') = c == c'
    let hash c = Hashtbl.hash c
  end

  module CircuitStructuralHashcons = Hashcons.Make(CircuitHash)
  module CircuitPhysicalHashcons = Hashcons.Make(CircuitPhysicalHash)

  module CoqStringSet = Set.Make(struct type t = char list let compare = poly_cmp end)

  module PhysicalHashTable (Params: sig type t end) =
    Hashtbl.Make(struct
        type t = Params.t
        let equal o1 o2 = o1 == o2
        let hash o = Hashtbl.hash o
      end)

  let dedup_circuit (type rule_name_t reg_t ext_fn_t)
        (pkg: (rule_name_t, reg_t, ext_fn_t) dedup_input_t) : circuit_graph =
    (* BundleHash, ExtrCircuitHashtbl is used to detect and leverage existing physical sharing *)
    let module ExtrCircuitHashtbl =
      PhysicalHashTable(struct type t = (rule_name_t, reg_t, ext_fn_t) extr_circuit end) in
    let module ExtrBundleHashtbl =
      PhysicalHashTable(struct type t = (reg_t, (rule_name_t, reg_t, ext_fn_t) Extr.rwdata) Extr.context end) in
    (* CircuitHashcons is used to find duplicate subcircuits *)
    let (module CircuitHashcons: Hashcons.S with type key = circuit') =
      if hashcons_circuits then (module CircuitStructuralHashcons)
      else (module CircuitPhysicalHashcons) in

    let list_of_hashcons hc =
      let acc = ref [] in
      CircuitHashcons.iter (fun e -> acc := e :: !acc) hc;
      !acc in

    let circuit_to_deduplicated = ExtrCircuitHashtbl.create 50 in
    let deduplicated_circuits = CircuitHashcons.create 50 in
    let bundles = ExtrBundleHashtbl.create 8 in

    let rec rebuild_circuit_for_deduplication (c0: (rule_name_t, reg_t, ext_fn_t) extr_circuit) =
      match c0 with
      | Extr.CMux (sz, s, c1, c2) ->
         CMux (sz, dedup s, dedup c1, dedup c2)
      | Extr.CConst (sz, bs) ->
         CConst (Util.array_of_vect sz bs)
      | Extr.CReadRegister r ->
         CReadRegister (pkg.di_reg_sigs r)
      | Extr.CUnop (fn, c1) ->
         CUnop (fn, dedup c1)
      | Extr.CBinop (fn, c1, c2) ->
         CBinop (fn, dedup c1, dedup c2)
      | Extr.CExternal (fn, c1) ->
         let f, kind = pkg.di_fn_specs fn in
         CExternal { f; internal = kind = `Internal; arg = dedup c1 }
      | Extr.CBundleRef (sz, rule_name, regs, bundle, field, circuit) ->
         if pkg.di_rule_external rule_name then
           let cbundle =
             match ExtrBundleHashtbl.find_opt bundles bundle with
             | Some c -> c
             | None ->
                let cbundle =
                  CBundle (pkg.di_rule_names rule_name,
                           Extr.mmap regs (fun r m ->
                               let rwdata = Extr.cassoc regs r m bundle in
                               (pkg.di_reg_sigs r, rebuild_rwdata_for_deduplication rwdata))) in
                ExtrBundleHashtbl.replace bundles bundle cbundle;
                cbundle in
           CBundleRef(sz, hashcons cbundle, rwcircuit_of_extr_rwcircuit pkg.di_reg_sigs field)
         else
           rebuild_circuit_for_deduplication circuit
      | Extr.CAnnot (sz, annot, c) ->
         if pkg.di_strip_annotations then
           rebuild_circuit_for_deduplication c
         else
           CAnnot (sz, Util.string_of_coq_string annot, dedup c)
    and rebuild_rwdata_for_deduplication (rw : (rule_name_t, reg_t, ext_fn_t) Extr.rwdata) =
      { read0 = dedup rw.read0;
        read1 = dedup rw.read1;
        write0 = dedup rw.write0;
        write1 = dedup rw.write1;
        data0 = dedup rw.data0;
        data1 = dedup rw.data1; }
    and dedup (c: (rule_name_t, reg_t, ext_fn_t) extr_circuit) =
      match ExtrCircuitHashtbl.find_opt circuit_to_deduplicated c with
      | Some c' -> c'
      | None ->
         let circuit = hashcons (rebuild_circuit_for_deduplication c) in
         ExtrCircuitHashtbl.add circuit_to_deduplicated c circuit;
         circuit
    and hashcons c =
      CircuitHashcons.hashcons deduplicated_circuits c in
    let _interesting_register r =
      let nm = (pkg.di_reg_sigs r).reg_name in
      let matches haystack needle =
        Str.string_match (Str.regexp needle) haystack 0 in
      matches nm "scoreboard_Scores_rData_[0-8]$" in
    let interesting_register _ = true in
    let graph_roots =
      Perf.with_timer "graph:dedup" (fun () ->
          List.map (fun reg ->
              let c = pkg.di_circuits reg in
              let r = pkg.di_reg_sigs reg in
              { root_reg = r;
                root_circuit =
                  (* Perf.with_timer (Printf.sprintf "graph:dedup:%s" r.reg_name) (fun () -> *)
                  if interesting_register reg then dedup c
                  else hashcons (CConst (Util.bits_of_value r.reg_init)) })
            pkg.di_regs) in
    let graph_nodes = list_of_hashcons deduplicated_circuits in
    let cmp (x: circuit) (y: circuit) = compare x.tag y.tag in
    let graph_nodes = List.stable_sort cmp graph_nodes in
    { graph_roots; graph_nodes }

  let graph_of_compile_unit (cu: 'f Compilation.compile_unit)
      : circuit_graph =
    let externalp rln = fst (List.assoc rln cu.c_rules) = `ExternalRule in
    let circuits = Perf.with_timer "graph:compile_unit" (fun () ->
                       Compilation.compile cu) in
    dedup_circuit
      { di_regs = cu.c_registers;
        di_reg_sigs = (fun r -> r);
        di_fn_specs = (fun fn -> (fn, `Internal));
        di_rule_names = (fun rln -> rln);
        di_rule_external = externalp;
        di_circuits = circuits;
        di_strip_annotations = strip_annotations }

  let graph_of_verilog_package (type pos_t var_t fn_name_t rule_name_t reg_t ext_fn_t)
        (kp: (pos_t, var_t, fn_name_t, rule_name_t, reg_t, ext_fn_t) Extr.koika_package_t)
        (vp: ext_fn_t Extr.verilog_package_t)
      : circuit_graph =
    let di_regs =
      kp.koika_reg_finite.finite_elements in
    let di_circuits =
      let cp = Perf.with_timer "graph:compile_koika_package" (fun () ->
                   Extr.compile_koika_package kp
                     (Compilation.opt kp.koika_reg_types kp.koika_ext_fn_types)) in
      fun r -> Extr.getenv cp.cp_reg_Env cp.cp_circuits r in
    let di_fn_specs f =
      let fn_sig = kp.koika_ext_fn_types f in
      let spec = vp.vp_ext_fn_specs f in
      let name = Util.string_of_coq_string spec.efr_name in
      (Util.ffi_sig_of_extr_external_sig name fn_sig,
       if spec.efr_internal then `Internal else `External) in
    dedup_circuit
      { di_regs;
        di_reg_sigs = Util.reg_sigs_of_koika_package kp;
        di_rule_names = (fun rln -> Util.string_of_coq_string @@ kp.koika_rule_names.show0 rln);
        di_rule_external = kp.koika_rule_external;
        di_fn_specs;
        di_circuits;
        di_strip_annotations = strip_annotations }
end
