type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

open Common
module SGA = SGA

module Util = struct
  let list_nth (l: 'a list) (n: SGA.index) =
    SGA.list_nth l n

  let string_of_coq_string chars =
    String.concat "" (List.map (String.make 1) chars)

  let coq_string_of_string s =
    List.of_seq (String.to_seq s)

  let bits_const_of_sga_bits sz bs =
    Array.of_list (SGA.vect_to_list sz bs)

  let sga_bits_of_bits_const (bs: bits_value) =
    SGA.vect_of_list (Array.to_list bs)

  let rec typ_of_sga_type (tau: SGA.type0) : typ =
    match tau with
    | SGA.Bits_t sz -> Bits_t sz
    | SGA.Enum_t sg -> Enum_t (enum_sig_of_sga_enum_sig sg)
    | SGA.Struct_t sg -> Struct_t (struct_sig_of_sga_struct_sig sg)
  and struct_sig_of_sga_struct_sig { struct_name; struct_fields } : struct_sig =
    { struct_name = string_of_coq_string struct_name;
      struct_fields = List.map (fun (nm, tau) ->
                          (string_of_coq_string nm, typ_of_sga_type tau))
                        struct_fields }
  and enum_sig_of_sga_enum_sig { enum_name; enum_size; enum_bitsize; enum_members; enum_bitpatterns } : enum_sig =
    { enum_name = string_of_coq_string enum_name;
      enum_bitsize = enum_bitsize;
      enum_members =
        List.map (fun (nm, bs) ->
            (string_of_coq_string nm, bits_const_of_sga_bits enum_bitsize bs))
          (SGA.vect_to_list enum_size (SGA.vect_zip enum_size enum_members enum_bitpatterns)) }

  let rec sga_type_of_typ (tau: typ) : SGA.type0 =
    match tau with
    | Bits_t sz -> SGA.Bits_t sz
    | Enum_t sg -> SGA.Enum_t (sga_enum_sig_of_enum_sig sg)
    | Struct_t sg -> SGA.Struct_t (sga_struct_sig_of_struct_sig sg)
  and sga_struct_sig_of_struct_sig { struct_name; struct_fields } : SGA.type0 SGA.struct_sig' =
    { struct_name = coq_string_of_string struct_name;
      struct_fields = List.map (fun (nm, tau) ->
                          (coq_string_of_string nm, sga_type_of_typ tau))
                        struct_fields }
  and sga_enum_sig_of_enum_sig { enum_name; enum_bitsize; enum_members } : SGA.enum_sig =
    { enum_name = coq_string_of_string enum_name;
      enum_bitsize = enum_bitsize;
      enum_size = List.length enum_members;
      enum_members = SGA.vect_of_list (List.map (fun (nm, _) -> coq_string_of_string nm) enum_members);
      enum_bitpatterns = SGA.vect_of_list (List.map (fun (_, bs) -> sga_bits_of_bits_const bs) enum_members) }

  let ffi_sig_of_sga_external_sig ffi_name fsig =
    SGA.{ ffi_name;
          ffi_arg1type = typ_of_sga_type fsig.arg1Type;
          ffi_arg2type = typ_of_sga_type fsig.arg2Type;
          ffi_rettype = typ_of_sga_type fsig.retType }

  let sga_external_sig_of_ffi_sig { ffi_arg1type; ffi_arg2type; ffi_rettype; _ } =
    SGA.{ arg1Type = sga_type_of_typ ffi_arg1type;
          arg2Type = sga_type_of_typ ffi_arg2type;
          retType = sga_type_of_typ ffi_rettype }

  let sga_type_to_string tau =
    typ_to_string (typ_of_sga_type tau)

  let sga_struct_sig_to_string sg =
    struct_sig_to_string (struct_sig_of_sga_struct_sig sg)

  let sga_enum_sig_to_string sg =
    enum_sig_to_string (enum_sig_of_sga_enum_sig sg)

  let type_kind_to_string (tk: SGA.type_kind) =
    match tk with
    | SGA.Kind_bits -> "bits"
    | SGA.Kind_enum None -> "enum"
    | SGA.Kind_enum (Some sg) -> sga_enum_sig_to_string sg
    | SGA.Kind_struct None -> "struct"
    | SGA.Kind_struct (Some sg) -> sga_struct_sig_to_string sg

  let string_eq_dec =
    { SGA.eq_dec = fun (s1: string) (s2: string) -> s1 = s2 }

  let type_error_to_error (epos: 'f) (err: _ SGA.error_message) =
    let ekind, emsg = match err with
      | SGA.UnboundVariable var ->
         (`NameError, Printf.sprintf "Unbound variable `%s'" var)
      | SGA.UnboundField (field, sg) ->
         (`NameError, Printf.sprintf "Unbound field `%s' in structure `%s'"
                        (string_of_coq_string field) (sga_struct_sig_to_string sg))
      | SGA.UnboundEnumMember (name, sg) ->
         (`NameError, Printf.sprintf "Constant `%s' is not a member of enum `%s'"
                        (string_of_coq_string name) (sga_enum_sig_to_string sg))
      | SGA.TypeMismatch (_tsig, actual, _expr, expected) ->
         (`TypeError, Printf.sprintf "This term has type `%s', but `%s' was expected"
                        (sga_type_to_string actual) (sga_type_to_string expected))
      | SGA.KindMismatch (_tsig, actual, _expr, expected) ->
         (`TypeError, Printf.sprintf "This term has type `%s', but kind `%s' was expected"
                        (sga_type_to_string actual) (type_kind_to_string expected))
    in { epos; ekind; emsg }

  let ffi_sig_of_interop_fn ~custom_fn_info (fn: 'a SGA.interop_fn_t) =
    match fn with
    | SGA.PrimFn fn ->
       ffi_sig_of_sga_external_sig (PrimFn fn) (SGA.prim_Sigma fn)
    | SGA.CustomFn fn ->
       let ffi = custom_fn_info fn in
       { ffi with ffi_name = CustomFn ffi.ffi_name }

  let rec value_of_sga_value tau v =
    match tau with
    | SGA.Bits_t sz ->
       Bits (bits_const_of_sga_bits sz v)
    | SGA.Enum_t sg ->
       Enum (enum_sig_of_sga_enum_sig sg, bits_const_of_sga_bits sg.enum_bitsize v)
    | SGA.Struct_t sg ->
       Struct (struct_sig_of_sga_struct_sig sg,
               List.map snd (SGA.struct_to_list value_of_sga_value sg.struct_fields v))

  let rec sga_value_of_value (v: value) =
    match v with
    | Bits bs -> SGA.Bits_t (Array.length bs), (sga_bits_of_bits_const bs)
    | Enum (sg, v) -> SGA.Enum_t (sga_enum_sig_of_enum_sig sg), (sga_bits_of_bits_const v)
    | Struct (sg, sv) ->
       let vv = List.map2 (fun (nm, _) v -> coq_string_of_string nm, v) sg.struct_fields sv in
       let conv v = let tau, sga_v = sga_value_of_value v in SGA.ExistT (tau, sga_v) in
       (SGA.Struct_t (sga_struct_sig_of_struct_sig sg),
        SGA.struct_of_list conv vv)

  let bits_of_value (v: value) =
    let tau, v = sga_value_of_value v in
    bits_const_of_sga_bits (SGA.type_sz tau) (SGA.bits_of_value tau v)

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

  let reg_sigs_of_sga_package (pkg: _ SGA.sga_package_t) r =
    let init = value_of_sga_value (pkg.sga_reg_types r) (pkg.sga_reg_init r) in
    { reg_name = string_of_coq_string (pkg.sga_reg_names r);
      reg_init = init }

  let fn_sigs_of_sga_package custom_fn_names (pkg: _ SGA.sga_package_t) =
    let custom_fn_info fn =
      let name, fn = custom_fn_names fn, pkg.sga_custom_fn_types fn in
      ffi_sig_of_sga_external_sig name fn in
    fun fn -> ffi_sig_of_interop_fn ~custom_fn_info fn
end

module Compilation = struct
  let translate_port = function
    | 0 -> SGA.P0
    | 1 -> SGA.P1
    | _ -> assert false

  type 'f raw_action =
    ('f, ('f, value literal, reg_signature, (string ffi_signature) SGA.interop_ufn_t) action) locd

  type 'f translated_action =
    ('f, var_t, reg_signature, string ffi_signature SGA.interop_ufn_t) SGA.uaction

  let rec translate_action ({ lpos; lcnt }: 'f raw_action) : 'f translated_action =
    SGA.UAPos
      (lpos,
       match lcnt with
       | Skip -> SGA.uSkip
       | Fail tau -> SGA.UFail (Util.sga_type_of_typ tau)
       | Lit (Var v) -> SGA.UVar v
       | Lit (Const v) -> let tau, v = Util.sga_value_of_value v in SGA.UConst (tau, v)
       | Assign (v, expr) -> SGA.UAssign (v.lcnt, translate_action expr)
       | StructInit (sg, fields) ->
          SGA.uStructInit (Util.sga_struct_sig_of_struct_sig sg)
            (List.map (fun (nm, v) -> Util.coq_string_of_string nm.lcnt, translate_action v) fields)
       | Progn rs -> translate_seq rs
       | Let (bs, body) -> translate_bindings bs body
       | If (e, r, rs) -> SGA.UIf (translate_action e, translate_action r, translate_seq rs)
       (* FIXME syntax for when in typechecker? *)
       | When (e, rs) -> SGA.UIf (translate_action e, translate_seq rs, SGA.UFail (SGA.Bits_t 0))
       | Switch { operand; default; branches } ->
          let opname = (* gensym *) "switch_operand" in
          let opvar = locd_make operand.lpos (Lit (Var opname)) in
          let switch = SGA.uSwitch (translate_action opvar)
                        (translate_action default)
                        (List.map (fun (lbl, br) ->
                             translate_action lbl,
                             translate_action br)
                           branches) in
          SGA.UBind (opname, (translate_action operand), switch)
       | Read (port, reg) -> SGA.URead (translate_port port, reg.lcnt)
       | Write (port, reg, v) -> SGA.UWrite (translate_port port, reg.lcnt, translate_action v)
       | Call (fn, a1 :: a2 :: []) -> SGA.UCall (fn.lcnt, translate_action a1, translate_action a2)
       | Call (_, _) -> assert false)
  and translate_bindings bs body =
    match bs with
    | [] -> translate_seq body
    | (v, e) :: bs -> SGA.UBind (v.lcnt, translate_action e, translate_bindings bs body)
  and translate_seq rs =
    match rs with
    | [] -> SGA.uSkip
    | [r] -> translate_action r
    | r :: rs -> SGA.USeq (translate_action r, translate_seq rs)

  let rec translate_scheduler { lpos; lcnt } =
    SGA.USPos
      (lpos,
       match lcnt with
       | Done -> SGA.UDone
       | Sequence [] -> SGA.UDone
       | Sequence (r :: rs) ->
          SGA.UCons (r.lcnt, translate_scheduler { lpos; lcnt = Sequence rs })
       | Try (r, s1, s2) ->
          SGA.UTry (r.lcnt, translate_scheduler s1, translate_scheduler s2))

  let _R = fun rs -> Util.sga_type_of_typ (reg_type rs)
  let custom_Sigma fn = Util.sga_external_sig_of_ffi_sig fn
  let custom_uSigma fn _a1 _a2 = SGA.Success fn
  let interop_Sigma fn = SGA.interop_Sigma custom_Sigma fn
  let interop_uSigma fn = SGA.interop_uSigma custom_uSigma fn

  let rEnv_of_register_list tc_registers =
    let reg_indices = List.mapi (fun i x -> x.reg_name, i) tc_registers in
    let regmap = Hashtbl.of_seq (List.to_seq reg_indices) in
    SGA.contextEnv { SGA.finite_elements = tc_registers;
                     SGA.finite_index = fun r -> Hashtbl.find regmap r.reg_name }

  type typechecked_action =
    (var_t, reg_signature, (string ffi_signature) SGA.interop_fn_t) SGA.action

  type 'f raw_scheduler = ('f, 'f scheduler) locd

  type typechecked_scheduler = var_t SGA.scheduler

  (* FIXME hashmaps, not lists *)
  type compile_unit =
    { c_registers: reg_signature list;
      c_scheduler: string SGA.scheduler;
      c_rules: (name_t * typechecked_action) list }

  type 'k compiled_circuit =
    (reg_signature, 'k SGA.interop_fn_t) SGA.circuit

  let typecheck_scheduler (raw_ast: 'f raw_scheduler) : var_t SGA.scheduler =
    let ast = translate_scheduler raw_ast in
    SGA.type_scheduler raw_ast.lpos ast

  let result_of_type_result = function
    | SGA.Success s -> Ok s
    | SGA.Failure ({ epos; emsg }: _ SGA.error) ->
       Error (Util.type_error_to_error epos emsg)

  let typecheck_rule (raw_ast: 'f raw_action) : (typechecked_action, 'f err_contents) result =
    let ast = translate_action raw_ast in
    match SGA.type_action Util.string_eq_dec _R interop_Sigma interop_uSigma raw_ast.lpos [] ast with
    | Success (SGA.ExistT (tau, r)) ->
       if tau = Bits_t 0 then Ok r
       else
         let msg =
           Printf.sprintf "This expression has type %s, but rules are expected to have type %s."
             (Util.sga_type_to_string tau) (Util.sga_type_to_string (Bits_t 0)) in
         Error { epos = raw_ast.lpos; ekind = `TypeError; emsg = msg }
    | Failure { epos; emsg } ->
       Error (Util.type_error_to_error epos emsg)

  let compile (cu: compile_unit) : (reg_signature -> 'k compiled_circuit) =
    let rEnv = rEnv_of_register_list cu.c_registers in
    let r0: _ SGA.env_t = SGA.create rEnv (fun r -> SGA.CReadRegister r) in
    let rules r = List.assoc r cu.c_rules in
    let opt = SGA.interop_opt _R custom_Sigma in
    let env = SGA.compile_scheduler _R interop_Sigma rEnv opt r0 rules cu.c_scheduler in
    (fun r -> SGA.getenv rEnv env r)
end

module Graphs = struct
  type ('p, 'k) circuit_graph = {
      graph_roots: ('p, 'k) fun_id_t circuit_root list;
      graph_nodes: ('p, 'k) fun_id_t circuit list
    }

  type ('prim, 'custom, 'reg_t, 'fn_t) dedup_input_t = {
      di_regs: 'reg_t list;
      di_reg_sigs: 'reg_t -> reg_signature;
      di_fn_sigs: 'fn_t -> ('prim, 'custom) fun_id_t ffi_signature;
      di_circuits : 'reg_t -> ('reg_t, 'fn_t) SGA.circuit
    }

  let dedup_circuit (type prim custom reg_t fn_t)
        (pkg: (prim, custom, reg_t, fn_t) dedup_input_t) : (prim, custom) circuit_graph =
    let module CircuitHash = struct
        type t = (prim, custom) fun_id_t circuit'
        let equal (c: (prim, custom) fun_id_t circuit') (c': (prim, custom) fun_id_t circuit') =
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
          | CExternal (f, a1, a2), CExternal (f', a1', a2') ->
             f = f' (* Not hashconsed *) && a1 == a1' && a2 == a2'
          | CReadRegister r, CReadRegister r' ->
             r = r' (* Not hashconsed *)
          | CAnnot (_, s, c), CAnnot (_, s', c') ->
             s = s' (* Not hashconsed *) && c == c'
          | _, _ -> false
        let hash c =
          Hashtbl.hash c
      end in
    let module SGACircuitHash = struct
        type t = (reg_t, fn_t) SGA.circuit
        let equal o1 o2 = o1 == o2
        let hash o = Hashtbl.hash o
      end in
    let module HasconsedOrder = struct
        type t = (prim, custom) fun_id_t circuit
        let compare x y = compare x.Hashcons.tag y.Hashcons.tag
      end in
    let module CircuitBag = Set.Make(HasconsedOrder) in
    let module CircuitHashcons = Hashcons.Make(CircuitHash) in
    let module SGACircuitHashtbl = Hashtbl.Make(SGACircuitHash) in

    let circuit_to_tagged = SGACircuitHashtbl.create 50 in
    let unique_tagged = CircuitHashcons.create 50 in
    let tagged_circuits = ref CircuitBag.empty in

    let rec aux (c: _ SGA.circuit) =
      match SGACircuitHashtbl.find_opt circuit_to_tagged c with
      | Some c' ->
         c'
      | None ->
         let circuit' =
           match c with
           | SGA.CNot c ->
              CNot (aux c)
           | SGA.CAnd (c1, c2) ->
              CAnd (aux c1, aux c2)
           | SGA.COr (c1, c2) ->
              COr (aux c1, aux c2)
           | SGA.CMux (sz, s, c1, c2) ->
              CMux (sz, aux s, aux c1, aux c2)
           | SGA.CConst (sz, bs) ->
              CConst (Util.bits_const_of_sga_bits sz bs)
           | SGA.CExternal (fn, c1, c2) ->
              CExternal (pkg.di_fn_sigs fn, aux c1, aux c2)
           | SGA.CReadRegister r ->
              CReadRegister (pkg.di_reg_sigs r)
           | SGA.CAnnot (sz, annot, c) ->
              CAnnot (sz, Util.string_of_coq_string annot, aux c) in
         let circuit = CircuitHashcons.hashcons unique_tagged circuit' in
         tagged_circuits := CircuitBag.add circuit !tagged_circuits;
         SGACircuitHashtbl.add circuit_to_tagged c circuit;
         circuit in
    let graph_roots = List.map (fun reg ->
                          let c = pkg.di_circuits reg in
                          { root_reg = pkg.di_reg_sigs reg;
                            root_circuit = aux c })
                        pkg.di_regs in
    let graph_nodes = List.of_seq (CircuitBag.to_seq !tagged_circuits) in
    { graph_roots; graph_nodes }

  let graph_of_compile_unit (cu: Compilation.compile_unit) : (SGA.prim_fn_t, string) circuit_graph =
    dedup_circuit
      { di_regs = cu.c_registers;
        di_reg_sigs = (fun r -> r);
        di_fn_sigs = (fun fn -> Util.ffi_sig_of_interop_fn ~custom_fn_info:(fun f -> f) fn);
        di_circuits = Compilation.compile cu }

  let graph_of_verilog_package (vp: _ SGA.verilog_package_t) =
    let sga = vp.vp_pkg in
    let di_regs =
      sga.sga_reg_finite.finite_elements in
    let di_circuits =
      let cp = SGA.compile_sga_package sga in
      fun r -> SGA.getenv cp.cp_reg_Env cp.cp_circuit r in
    let custom_fn_names f =
      Util.string_of_coq_string (vp.vp_custom_fn_names f) in
    dedup_circuit
      { di_regs;
        di_reg_sigs = Util.reg_sigs_of_sga_package sga;
        di_fn_sigs = Util.fn_sigs_of_sga_package custom_fn_names sga; di_circuits }
end
