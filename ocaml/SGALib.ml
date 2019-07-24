type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

open Common

type ('prim, 'reg_t, 'fn_t) dedup_input_t = {
    di_regs: 'reg_t list;
    di_reg_sigs: 'reg_t -> reg_signature;
    di_fn_sigs: 'fn_t -> 'prim ffi_signature;
    di_circuits : 'reg_t -> ('reg_t, 'fn_t) SGA.circuit
  }

module SGA = SGA

module Util = struct
  let type_to_string (tau: SGA.type0) =
    Printf.sprintf "bits %d" tau

  let string_eq_dec (s1: string) (s2: string) =
    s1 = s2

  let string_of_bits bs =
    let bitstring = String.concat "" (List.rev_map (fun b -> if b then "1" else "0") bs.bs_bits) in
    Printf.sprintf "%d'b%s" bs.bs_size bitstring

  let string_of_coq_string chars =
    String.concat "" (List.map (String.make 1) chars)

  let type_error_to_error (epos: pos_t) (err: _ SGA.error_message) =
    let ekind, emsg = match err with
      | SGA.UnboundVariable var ->
         (`NameError, Printf.sprintf "Unbound variable `%s'" var)
      | SGA.TypeMismatch (_tsig, actual, _expr, expected) ->
         (`TypeError, Printf.sprintf "Inferred type %s does not match expected type %s"
                        (type_to_string actual) (type_to_string expected))
    in Error { epos = epos; ekind = ekind; emsg = emsg }

  let bits_const_of_bits sz bs =
    { bs_size = sz;
      bs_bits = SGA.vect_to_list sz bs }

  let bits_const_to_int bs =
    List.fold_right (fun b bs -> (if b then 1 else 0) + 2 * bs) bs.bs_bits 0

  let dedup_input_of_tc_unit { tc_registers; _ } circuits =
    { di_regs = tc_registers;
      di_reg_sigs = (fun r -> r);
      di_fn_sigs = (fun fn -> fn);
      di_circuits = circuits }

  let dedup_input_of_verilogPackage (pkg: SGA.verilogPackage) =
    let di_regs =
      pkg.vp_reg_finite.finite_elems in
    let di_reg_sigs r =
      let sz = pkg.vp_reg_types r in
      { reg_name = string_of_coq_string (pkg.vp_reg_names r);
        reg_size = sz;
        reg_init_val = bits_const_of_bits sz (pkg.vp_reg_init r) } in
    let di_fn_sigs fn =
      let ffi_name, fsig = match fn with
      | SGA.PrimFn fn ->
         PrimFn fn,
         SGA.prim_Sigma fn
      | SGA.CustomFn fn ->
         CustomFn (string_of_coq_string (pkg.vp_custom_fn_names fn)),
         pkg.vp_custom_fn_types fn in
      { ffi_name;
        ffi_arg1size = fsig.arg1Type;
        ffi_arg2size = fsig.arg2Type;
        ffi_retsize = fsig.retType } in
    let di_circuits r =
      SGA.getenv pkg.vp_reg_Env pkg.vp_circuit r in
    { di_regs; di_reg_sigs; di_fn_sigs; di_circuits }
end

module Compilation = struct
  let translate_expr_ast raw_ast =
    Obj.magic ()

  let translate_rule_ast raw_ast =
    Obj.magic ()

  let translate_scheduler_ast raw_ast =
    Obj.magic ()

  let r = fun rs ->
    rs.reg_size

  let sigma = fun fn ->
    { SGA.arg1Type = fn.ffi_arg1size;
      SGA.arg2Type = fn.ffi_arg2size;
      SGA.retType = fn.ffi_retsize }

  let rEnv_of_tc_unit { tc_registers; _ } =
    let eqdec r1 r2 = Util.string_eq_dec r1.reg_name r2.reg_name in
    SGA.contextEnv { SGA.finite_elems = tc_registers; (* TODO memoize call to mem *)
                     SGA.finite_index = fun rn -> match SGA.mem eqdec rn tc_registers with
                                                  | Inl m -> m
                                                  | Inr _ -> failwith "Unexpected register name" }

  let compile tc_unit raw_ast : (reg_signature -> (reg_signature, 'prim ffi_signature) SGA.circuit) =
    let ast = translate_scheduler_ast raw_ast in
    let rEnv = rEnv_of_tc_unit tc_unit in
    let r0: _ SGA.env_t = rEnv.create __ (fun r -> Obj.magic (CReadRegister r)) in
    match SGA.type_scheduler Util.string_eq_dec r sigma (Obj.magic "pos spanning whole doc") ast with
    | WellTyped s ->
       let env = SGA.compile_scheduler r sigma rEnv r0 s in
       (fun r -> SGA.getenv rEnv env r)
    | IllTyped { epos; emsg } ->
       raise (Util.type_error_to_error epos emsg)
end

module Graphs = struct
  module CircuitHash =
    struct
      type t = Obj.t
      let equal o1 o2 = o1 == o2
      let hash o = Hashtbl.hash o
    end

  module CircuitHashtbl = Hashtbl.Make(CircuitHash)

  type 'prim circuit_graph = {
      graph_roots: circuit_root list;
      graph_ptrs: 'prim circuit PtrHashtbl.t
    }

  let dedup_circuit (pkg: ('prim, 'reg_t, 'fn_t) dedup_input_t) : 'prim circuit_graph =
    let circuit_to_ptr = CircuitHashtbl.create 50 in
    let ptr_to_object = PtrHashtbl.create 50 in
    let nextptr = ref 0 in
    let rec aux (c: _ SGA.circuit) =
      match CircuitHashtbl.find_opt circuit_to_ptr (Obj.magic c) with
      | Some ptr -> ptr
      | None ->
         let ptr = !nextptr in
         incr nextptr;
         let deduplicated =
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
              CConst (Util.bits_const_of_bits sz bs)
           | SGA.CExternal (fn, c1, c2) ->
              CExternal (pkg.di_fn_sigs fn, aux c1, aux c2)
           | SGA.CReadRegister r ->
              CReadRegister (pkg.di_reg_sigs r)
           | SGA.CAnnot (sz, annot, c) ->
              CAnnot (sz, Util.string_of_coq_string annot, aux c)
         in
         CircuitHashtbl.add circuit_to_ptr (Obj.magic c) ptr;
         PtrHashtbl.add ptr_to_object ptr deduplicated;
         ptr in
    (* CircuitHashtbl.fold (fun k v acc -> (k, v) :: acc)  object_to_ptr [], *)
    (* PtrHashtbl.fold (fun k v acc -> (k, v) :: acc)  ptr_to_object []) *)
    { graph_roots = List.map (fun reg ->
                        let c = pkg.di_circuits reg in
                        { root_reg = pkg.di_reg_sigs reg;
                          root_ptr = aux c })
                      pkg.di_regs;
      graph_ptrs = ptr_to_object }
end
