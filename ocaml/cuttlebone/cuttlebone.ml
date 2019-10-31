type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

open Common
module Extr = Extr

type ('name_t, 'reg_t, 'ext_fn_t) extr_circuit =
  ('name_t, 'reg_t, 'ext_fn_t, ('name_t, 'reg_t, 'ext_fn_t) Extr.rwdata) Extr.circuit

module Util = struct
  let list_nth (l: 'a list) (n: Extr.index) =
    Extr.list_nth l n

  let string_of_coq_string chars =
    String.concat "" (List.map (String.make 1) chars)

  let coq_string_of_string s =
    List.of_seq (String.to_seq s)

  let bits_const_of_extr_bits sz bs =
    Array.of_list (Extr.vect_to_list sz bs)

  let extr_bits_of_bits_const (bs: bits_value) =
    Extr.vect_of_list (Array.to_list bs)

  let rec typ_of_extr_type (tau: Extr.type0) : typ =
    match tau with
    | Extr.Bits_t sz -> Bits_t sz
    | Extr.Enum_t sg -> Enum_t (enum_sig_of_extr_enum_sig sg)
    | Extr.Struct_t sg -> Struct_t (struct_sig_of_extr_struct_sig sg)
  and struct_sig_of_extr_struct_sig { struct_name; struct_fields } : struct_sig =
    { struct_name = string_of_coq_string struct_name;
      struct_fields = List.map (fun (nm, tau) ->
                          (string_of_coq_string nm, typ_of_extr_type tau))
                        struct_fields }
  and enum_sig_of_extr_enum_sig { enum_name; enum_size; enum_bitsize; enum_members; enum_bitpatterns } : enum_sig =
    { enum_name = string_of_coq_string enum_name;
      enum_bitsize = enum_bitsize;
      enum_members =
        List.map (fun (nm, bs) ->
            (string_of_coq_string nm, bits_const_of_extr_bits enum_bitsize bs))
          (Extr.vect_to_list enum_size (Extr.vect_zip enum_size enum_members enum_bitpatterns)) }

  let rec extr_type_of_typ (tau: typ) : Extr.type0 =
    match tau with
    | Bits_t sz -> Extr.Bits_t sz
    | Enum_t sg -> Extr.Enum_t (extr_enum_sig_of_enum_sig sg)
    | Struct_t sg -> Extr.Struct_t (extr_struct_sig_of_struct_sig sg)
  and extr_struct_sig_of_struct_sig { struct_name; struct_fields } : Extr.type0 Extr.struct_sig' =
    { struct_name = coq_string_of_string struct_name;
      struct_fields = List.map (fun (nm, tau) ->
                          (coq_string_of_string nm, extr_type_of_typ tau))
                        struct_fields }
  and extr_enum_sig_of_enum_sig { enum_name; enum_bitsize; enum_members } : Extr.enum_sig =
    { enum_name = coq_string_of_string enum_name;
      enum_bitsize = enum_bitsize;
      enum_size = List.length enum_members;
      enum_members = Extr.vect_of_list (List.map (fun (nm, _) -> coq_string_of_string nm) enum_members);
      enum_bitpatterns = Extr.vect_of_list (List.map (fun (_, bs) -> extr_bits_of_bits_const bs) enum_members) }

  let argType nargs (fsig: Extr.sig1) idx : typ =
    typ_of_extr_type @@ List.nth (Extr.vect_to_list nargs fsig.argTypes) idx

  let retType (fsig: Extr.sig1) : typ =
    typ_of_extr_type fsig.retType

  let ffi_sig_of_extr_external_sig ffi_name fsig =
    Extr.{ ffi_name;
          ffi_argtype = argType 1 fsig 0;
          ffi_rettype = typ_of_extr_type fsig.retType }

  let extr_external_sig_of_ffi_sig { ffi_argtype; ffi_rettype; _ } =
    Extr.{ argTypes = Extr.vect_of_list [extr_type_of_typ ffi_argtype];
          retType = extr_type_of_typ ffi_rettype }

  let extr_intfun_of_intfun fbody (fsig: _ Common.internal_function) =
    { Extr.int_name = fsig.int_name;
      Extr.int_argspec = List.map (fun (nm, tau) -> nm, extr_type_of_typ tau) fsig.int_argspec;
      Extr.int_retType = extr_type_of_typ fsig.int_retType;
      Extr.int_body = fbody fsig.int_body }

  let extr_type_to_string tau =
    typ_to_string (typ_of_extr_type tau)

  let extr_struct_sig_to_string sg =
    struct_sig_to_string (struct_sig_of_extr_struct_sig sg)

  let extr_enum_sig_to_string sg =
    enum_sig_to_string (enum_sig_of_extr_enum_sig sg)

  let type_kind_to_string (tk: Extr.type_kind) =
    match tk with
    | Extr.Kind_bits -> "bits"
    | Extr.Kind_enum None -> "enum"
    | Extr.Kind_enum (Some sg) -> extr_enum_sig_to_string sg
    | Extr.Kind_struct None -> "struct"
    | Extr.Kind_struct (Some sg) -> extr_struct_sig_to_string sg

  let string_eq_dec =
    { Extr.eq_dec = fun (s1: string) (s2: string) -> s1 = s2 }

  let any_eq_dec =
    { Extr.eq_dec = fun (s1: 'a) (s2: 'a) -> s1 = s2 }

  type 'var_t extr_error_message =
    | ExplicitErrorInAst
    | SugaredConstructorInAst
    | UnboundVariable of { var: 'var_t }
    | UnboundField of { field: string; sg: struct_sig }
    | UnboundEnumMember of { name: string; sg: enum_sig }
    | IncorrectRuleType of { actual: typ }
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
    | Extr.IncorrectRuleType tau ->
       IncorrectRuleType { actual = typ_of_extr_type tau }
    | Extr.TooManyArguments (name, expected, nextras) ->
       TooManyArguments { name; expected; actual = expected + nextras }
    | Extr.TooFewArguments (name, expected, nmissing) ->
       TooFewArguments { name; expected; actual = expected - nmissing }
    |Extr.BasicError err ->
      match err with
      | Extr.UnboundField (field, sg) ->
         UnboundField { field = string_of_coq_string field;
                        sg = struct_sig_of_extr_struct_sig sg }
      | Extr.TypeMismatch (actual, expected) ->
         TypeMismatch { actual = typ_of_extr_type actual;
                        expected = typ_of_extr_type expected }
      | Extr.KindMismatch (actual, expected) ->
         KindMismatch { actual = type_kind_to_string actual;
                        expected = type_kind_to_string expected }

  let rec value_of_extr_value tau v =
    match tau with
    | Extr.Bits_t sz ->
       Bits (bits_const_of_extr_bits sz v)
    | Extr.Enum_t sg ->
       Enum (enum_sig_of_extr_enum_sig sg, bits_const_of_extr_bits sg.enum_bitsize v)
    | Extr.Struct_t sg ->
       Struct (struct_sig_of_extr_struct_sig sg,
               List.map snd (Extr.struct_to_list value_of_extr_value sg.struct_fields v))

  let rec extr_value_of_value (v: value) =
    match v with
    | Bits bs -> Extr.Bits_t (Array.length bs), (extr_bits_of_bits_const bs)
    | Enum (sg, v) -> Extr.Enum_t (extr_enum_sig_of_enum_sig sg), (extr_bits_of_bits_const v)
    | Struct (sg, sv) ->
       let vv = List.map2 (fun (nm, _) v -> coq_string_of_string nm, v) sg.struct_fields sv in
       let conv v = let tau, extr_v = extr_value_of_value v in Extr.ExistT (tau, extr_v) in
       (Extr.Struct_t (extr_struct_sig_of_struct_sig sg),
        Extr.struct_of_list conv vv)

  let bits_of_value (v: value) =
    let tau, v = extr_value_of_value v in
    bits_const_of_extr_bits (Extr.type_sz tau) (Extr.bits_of_value tau v)

  let rec string_of_value (v: value) =
    match v with
    | Bits bs -> string_of_bits bs
    | Enum (sg, v) -> string_of_enum sg v
    | Struct (sg, v) -> string_of_struct sg v
  and string_of_bits ?(mode=`Verilog) (bs: bits_value) =
    let bitstring = String.concat "" (List.rev_map (fun b -> if b then "1" else "0") (Array.to_list bs)) in
    (match mode with
     | `Cpp -> Printf.sprintf "0b%s"
     | `Verilog -> Printf.sprintf "%d'b%s" (Array.length bs)) bitstring
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

  let reg_sigs_of_koika_package (pkg: _ Extr.koika_package_t) r =
    let init = value_of_extr_value (pkg.koika_reg_types r) (pkg.koika_reg_init r) in
    { reg_name = string_of_coq_string (pkg.koika_reg_names r);
      reg_init = init }

  (* let fn_sigs_of_koika_package ext_fn_names (pkg: _ Extr.koika_package_t) =
   *   let custom_fn_info fn =
   *     let name, fn = custom_fn_names fn, pkg.koika_ext_fn_types fn in
   *     ffi_sig_of_extr_external_sig name fn in
   *   fun fn -> ffi_sig_of_interop_fn ~custom_fn_info fn *)

  (* Not implemented in Extr because Extr needs an R and a Sigma to iterate through an action *)
  let rec exists_subterm (f: _ Extr.action -> bool) (a: _ Extr.action) =
    f a ||
      match a with
       | Fail _
       | Var _
       | Const _ -> false
       | Assign (_, _, _, _, ex) -> exists_subterm f ex
       | Seq (_, _, a1, a2) -> exists_subterm f a1 || exists_subterm f a2
       | Bind (_, _, _, _, ex, body) -> exists_subterm f ex || exists_subterm f body
       | If (_, _, cond, tbranch, fbranch) ->
          exists_subterm f cond || exists_subterm f tbranch || exists_subterm f fbranch
       | Read (_, _, _) -> false
       | Write (_, _, _, value) -> exists_subterm f value
       | Unop (_, _, a) -> exists_subterm f a
       | Binop (_, _, a1, a2) -> exists_subterm f a1 || exists_subterm f a2
       | ExternalCall (_, _, a) -> exists_subterm f a
       | APos (_, _, _, a) -> exists_subterm f a

  let action_mentions_var k a =
    exists_subterm (function
        | Var (_, k', _, _) -> k' = k
        | _ -> false) a

  let member_mentions_shadowed_binding sg k0 v0 (m: _ Extr.member) =
    Extr.member_mentions_shadowed_binding any_eq_dec sg k0 v0 m
end

module Compilation = struct
  let translate_port = function
    | P0 -> Extr.P0
    | P1 -> Extr.P1

  type 'f extr_uaction =
    ('f, fn_name_t, var_t, reg_signature, ffi_signature) Extr.uaction
  type 'f extr_uscheduler =
    ('f, rule_name_t) Extr.uscheduler

  type 'f extr_action = ('f, var_t, reg_signature, ffi_signature) Extr.action
  type 'f extr_rule = [ `ExternalRule | `InternalRule ] * 'f extr_action
  type 'f extr_scheduler = ('f, var_t) Extr.scheduler

  let _R = fun rs -> Util.extr_type_of_typ (reg_type rs)
  let _Sigma fn = Util.extr_external_sig_of_ffi_sig fn

  let finiteType_of_register_list tc_registers =
    let reg_indices = List.mapi (fun i x -> x.reg_name, i) tc_registers in
    let regmap = Hashtbl.of_seq (List.to_seq reg_indices) in
    { Extr.finite_elements = tc_registers;
      Extr.finite_index = fun r -> Hashtbl.find regmap r.reg_name }

  (* FIXME hashmaps, not lists *)
  type 'f compile_unit =
    { c_registers: reg_signature list;
      c_scheduler: ('f, string) Extr.scheduler;
      c_rules: (rule_name_t * 'f extr_rule) list;
      c_cpp_preamble: string option;
      c_pos_of_pos: 'f -> Pos.t }

  type compiled_circuit =
    (string, reg_signature, ffi_signature) extr_circuit

  let typecheck_scheduler pos (ast: 'f extr_uscheduler) : 'f extr_scheduler =
    Extr.type_scheduler pos ast

  let result_of_type_result = function
    | Extr.Success s -> Ok s
    | Extr.Failure (err: _ Extr.error) -> Error (err.epos, Util.translate_extr_error_message err.emsg)

  let typecheck_rule pos (ast: 'f extr_uaction) : ('f extr_action, ('f * _)) result =
    Extr.type_rule Util.string_eq_dec _R _Sigma pos (Extr.desugar_action pos ast)
    |> result_of_type_result

  let compile (cu: 'f compile_unit) : (reg_signature -> compiled_circuit) =
    let finiteType = finiteType_of_register_list cu.c_registers in
    let rules r = List.assoc r cu.c_rules |> snd in
    let rEnv = Extr.contextEnv finiteType in
    let env = Extr.compile_scheduler _R _Sigma finiteType rules cu.c_scheduler in
    (fun r -> Extr.getenv rEnv env r)
end

module Graphs = struct
  type circuit = circuit' Hashcons.hash_consed
  and circuit' =
    | CNot of circuit
    | CAnd of circuit * circuit
    | COr of circuit * circuit
    | CMux of int * circuit * circuit * circuit
    | CConst of bits_value
    | CReadRegister of reg_signature
    | CUnop of Extr.PrimTyped.fbits1 * circuit
    | CBinop of Extr.PrimTyped.fbits2 * circuit * circuit
    | CExternal of ffi_signature * circuit
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
      di_fn_sigs: 'ext_fn_t -> ffi_signature;
      di_rule_names: 'rule_name_t -> string;
      di_external_rules: 'rule_name_t list;
      di_circuits : 'reg_t -> ('rule_name_t, 'reg_t, 'ext_fn_t) extr_circuit
    }

  module CircuitHash = struct
    type t = circuit'
    let rec equal (c: circuit') (c': circuit') =
      match c, c' with
      | CNot c1, CNot c1' ->
         c1 == c1'
      | CAnd (c1, c2), CAnd (c1', c2') ->
         c1 == c1' && c2 == c2'
      | COr (c1, c2), COr (c1', c2') ->
         c1 == c1' && c2 == c2'
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
      | CExternal (f, a1), CExternal (f', a1') ->
         f = f' (* Not hashconsed *) && a1 == a1'
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
    let hash c =
      Hashtbl.hash c
  end

  (* CircuitHashcons is used to find duplicate subcircuits *)
  module CircuitHashcons = Hashcons.Make(CircuitHash)

  let dedup_circuit (type rule_name_t reg_t ext_fn_t)
        (pkg: (rule_name_t, reg_t, ext_fn_t) dedup_input_t) : circuit_graph =
    let module ExtrCircuitHash = struct
        type t = (rule_name_t, reg_t, ext_fn_t) extr_circuit
        let equal o1 o2 = o1 == o2
        let hash o = Hashtbl.hash o
      end in
    (* ExtrCircuitHashtbl is used to detect and leverage existing physical sharing *)
    let module ExtrCircuitHashtbl = Hashtbl.Make(ExtrCircuitHash) in

    let list_of_hashcons hc =
      let acc = ref [] in
      CircuitHashcons.iter (fun e -> acc := e :: !acc) hc;
      !acc in

    let circuit_to_deduplicated = ExtrCircuitHashtbl.create 50 in
    let deduplicated_circuits = CircuitHashcons.create 50 in

    let rec rebuild_circuit_for_deduplication (c: (rule_name_t, reg_t, ext_fn_t) extr_circuit) =
      match c with
      | Extr.CNot c ->
         CNot (dedup c)
      | Extr.CAnd (c1, c2) ->
         CAnd (dedup c1, dedup c2)
      | Extr.COr (c1, c2) ->
         COr (dedup c1, dedup c2)
      | Extr.CMux (sz, s, c1, c2) ->
         CMux (sz, dedup s, dedup c1, dedup c2)
      | Extr.CConst (sz, bs) ->
         CConst (Util.bits_const_of_extr_bits sz bs)
      | Extr.CReadRegister r ->
         CReadRegister (pkg.di_reg_sigs r)
      | Extr.CUnop (fn, c1) ->
         CUnop (fn, dedup c1)
      | Extr.CBinop (fn, c1, c2) ->
         CBinop (fn, dedup c1, dedup c2)
      | Extr.CExternal (fn, c1) ->
         CExternal (pkg.di_fn_sigs fn, dedup c1)
      | Extr.CBundleRef (sz, rule_name, regs, bundle, field, circuit) ->
         let bundle =
           CBundle (pkg.di_rule_names rule_name,
                    Extr.mmap regs (fun r m ->
                        let rwdata = Extr.cassoc regs r m bundle in
                        (pkg.di_reg_sigs r, rebuild_rwdata_for_deduplication rwdata))) in
         if List.mem rule_name pkg.di_external_rules then
           CBundleRef(sz, hashcons bundle, rwcircuit_of_extr_rwcircuit pkg.di_reg_sigs field)
         else
           rebuild_circuit_for_deduplication circuit
      | Extr.CAnnot (sz, annot, c) ->
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
    let graph_roots = List.map (fun reg ->
                          let c = pkg.di_circuits reg in
                          { root_reg = pkg.di_reg_sigs reg;
                            root_circuit = dedup c })
                        pkg.di_regs in
    let graph_nodes = list_of_hashcons deduplicated_circuits in
    { graph_roots; graph_nodes }

  let graph_of_compile_unit (cu: 'f Compilation.compile_unit)
      : circuit_graph =
    let external_rules = List.filter (fun (_, (kind, _)) -> kind = `ExternalRule) cu.c_rules in
    dedup_circuit
      { di_regs = cu.c_registers;
        di_reg_sigs = (fun r -> r);
        di_fn_sigs = (fun fn -> fn);
        di_rule_names = (fun rln -> rln);
        di_external_rules = List.map fst external_rules;
        di_circuits = Compilation.compile cu }

  let graph_of_verilog_package (type pos_t var_t rule_name_t reg_t ext_fn_t)
        (kp: (pos_t, var_t, rule_name_t, reg_t, ext_fn_t) Extr.koika_package_t)
        (vp: (rule_name_t, ext_fn_t) Extr.verilog_package_t)
      : circuit_graph =
    let di_regs =
      kp.koika_reg_finite.finite_elements in
    let di_circuits =
      let cp = Extr.compile_koika_package kp in
      fun r -> Extr.getenv cp.cp_reg_Env cp.cp_circuits r in
    let di_fn_sigs f =
      let fn_name = Util.string_of_coq_string (vp.vp_ext_fn_names f) in
      let fn_sig = kp.koika_ext_fn_types f in
      Util.ffi_sig_of_extr_external_sig fn_name fn_sig in
    dedup_circuit
      { di_regs;
        di_reg_sigs = Util.reg_sigs_of_koika_package kp;
        di_rule_names = (fun rln -> Util.string_of_coq_string @@ kp.koika_rule_names rln);
        di_external_rules = vp.vp_external_rules;
        di_fn_sigs;
        di_circuits }
end
