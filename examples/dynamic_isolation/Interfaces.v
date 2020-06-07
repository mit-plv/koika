Require Import Koika.Frontend.
Require Import Coq.Lists.List.

Require Import Koika.Std.

Require Import dynamic_isolation.Lift.
Require Import dynamic_isolation.Tactics.
Require Import dynamic_isolation.Scoreboard.

Definition post_t := unit.
Definition var_t := string.
Definition fn_name_t := string.

(* Our machine consists of two cores, a security monitor, a memory hierarchy, and external memory modules.
 * We have a well-defined interface to each component.
 *)

Module Common.

  Definition mem_req :=
    {| struct_name := "mem_req";
       struct_fields := [("byte_en" , bits_t 4);
                         ("addr"     , bits_t 32);
                         ("data"     , bits_t 32)] |}.

  Definition mem_req_get_addr (req: struct_t mem_req) : bits_t 32 :=
    let '(_, (addr, (_, _))) := req in
    addr.


  Definition mem_resp :=
    {| struct_name := "mem_resp";
       struct_fields := [("byte_en", bits_t 4); ("addr", bits_t 32); ("data", bits_t 32)] |}.

  Inductive enclave_id :=
  | Enclave0
  | Enclave1
  | Enclave2
  | Enclave3.

  Definition enclave_req :=
    {| struct_name := "enclave_req";
       struct_fields := [("eid", bits_t 32)]
    |}.

  Module FifoMemReq <: Fifo.
    Definition T:= struct_t mem_req.
  End FifoMemReq.
  Module MemReq := Fifo1Bypass FifoMemReq.

  Module FifoMemResp <: Fifo.
    Definition T:= struct_t mem_resp.
  End FifoMemResp.
  Module MemResp := Fifo1 FifoMemResp.

  Module FifoEnclaveReq <: Fifo.
    Definition T := struct_t enclave_req.
  End FifoEnclaveReq.
  Module EnclaveReq := Fifo1Bypass FifoEnclaveReq.

  Instance FiniteType_MemReq : FiniteType MemReq.reg_t := _.
  Instance FiniteType_MemResp : FiniteType MemResp.reg_t := _.
  Instance FiniteType_FifoEnclaveReq : FiniteType EnclaveReq.reg_t := _.

  Inductive ind_core_id :=
  | CoreId0
  | CoreId1
  .

  Inductive ind_cache_type :=
  | CacheType_Imem
  | CacheType_Dmem
  .

  Definition addr_t := bits_t 32.
  Definition data_t := bits_t 32.
  Definition core_id_t := bits_t 1.

  (* Alignment *)
  Definition addr_index_t := bits_t 30.

  Definition initial_mem_t := addr_index_t -> data_t.

  Definition mem_input :=
    {| struct_name := "mem_input";
       struct_fields := [("get_ready", bits_t 1);
                        ("put_valid", bits_t 1);
                        ("put_request", struct_t mem_req)] |}.

  Definition mem_output :=
    {| struct_name := "mem_output";
       struct_fields := [("get_valid", bits_t 1);
                        ("put_ready", bits_t 1);
                        ("get_response", struct_t mem_resp)] |}.

  Definition ENUM_purge_restart := Ob~0~0.
  Definition ENUM_purge_ready := Ob~0~1.
  Definition ENUM_purge_purging := Ob~1~0.
  Definition ENUM_purge_purged := Ob~1~1.

  Definition purge_state :=
    {| enum_name := "purge_state";
       enum_members := vect_of_list ["Restart"; "Ready"; "Purging"; "Purged"];
       enum_bitpatterns := vect_of_list [ENUM_purge_restart; ENUM_purge_ready; 
                                         ENUM_purge_purging; ENUM_purge_purged] |}.

  Module RfParams <: RfPow2_sig.
    Definition idx_sz := log2 32.
    Definition T := bits_t 32.
    Definition init := Bits.zeroes 32.
    Definition read_style := Scoreboard.read_style 32.
    Definition write_style := Scoreboard.write_style.
  End RfParams.
  Module Rf := RfPow2 RfParams.

  Instance FiniteType_rf : FiniteType Rf.reg_t := _.
   
End Common.

(* TODO: need a well-formed predicate *)
Module Type EnclaveParameters.
  Parameter enclave_base : Common.enclave_id -> Common.addr_t.
  Parameter enclave_size : Common.enclave_id -> bits_t 32.
  Parameter enclave_bootloader_addr : Common.enclave_id -> Common.addr_t.
End EnclaveParameters.

Module Type CoreParameters.
  Parameter core_id : Common.core_id_t.
  Parameter initial_pc : Common.addr_t.
End CoreParameters.

Module Type External_sig.
  Parameter ext_fn_t : Type.
  Parameter Sigma : ext_fn_t -> ExternalSignature.
  (* TODO: for later *)
  (* Parameter sigma : (forall fn: ext_fn_t, Sig_denote (Sigma fn)). *)
  Parameter ext_fn_specs : ext_fn_t -> ext_fn_spec.

End External_sig.

Module Type Core_sig (External: External_sig) (Params: EnclaveParameters) (CoreParams: CoreParameters).
  Import Common.
  Parameter internal_reg_t : Type.
  Parameter R_internal : internal_reg_t -> type.
  Parameter r_internal : forall (idx: internal_reg_t), R_internal idx.
  Declare Instance FiniteType_internal_reg_t : FiniteType internal_reg_t.

  Inductive reg_t :=
  | core_id
  | toIMem (state: MemReq.reg_t)
  | toDMem (state: MemReq.reg_t)
  | fromIMem (state: MemResp.reg_t)
  | fromDMem (state: MemResp.reg_t)
  | toSMEnc (state: EnclaveReq.reg_t)
  (* | rf (state: Rf.reg_t) *)
  | pc
  | purge
  | internal (r: internal_reg_t)
  .

  Definition R (idx: reg_t) : type :=
   match idx with
   | core_id => core_id_t
   | toIMem r => MemReq.R r
   | toDMem r => MemReq.R r
   | fromIMem  r => MemResp.R r
   | fromDMem  r => MemResp.R r
   | toSMEnc r => EnclaveReq.R r
   (* | rf r => Rf.R r  *)
   | pc => bits_t 32
   | purge => enum_t purge_state
   | internal r => R_internal r
   end.

  Definition r idx : R idx :=
    match idx with
    | core_id => CoreParams.core_id
    | toIMem s => MemReq.r s
    | fromIMem s => MemResp.r s
    | toDMem s => MemReq.r s
    | fromDMem s => MemResp.r s
    | toSMEnc s => EnclaveReq.r s
    (* | rf r => Rf.r r  *)
    | pc => CoreParams.initial_pc
    | purge => value_of_bits (Bits.zero)
    | internal s => r_internal s
    end.

  Declare Instance FiniteType_reg_t : FiniteType reg_t.

  Definition ext_fn_t := External.ext_fn_t.
  Definition Sigma := External.Sigma.
  Definition rule := rule R Sigma.
  (* Definition sigma := External.sigma. *)

  Parameter rule_name_t : Type.
  Parameter rules  : rule_name_t -> rule.

  Parameter schedule : Syntax.scheduler pos_t rule_name_t.

  Section CycleSemantics.
    Definition state := env_t ContextEnv (fun idx : reg_t => R idx).
    Definition empty_log : Log R ContextEnv := log_empty.

    Parameter update_function : state -> Log R ContextEnv -> Log R ContextEnv.
      (* interp_scheduler' st ? rules log scheduler. *)

  End CycleSemantics.

  Section LogHelpers.
    Definition update_no_writes_to_reg (st: state) (log: Log R ContextEnv) (reg: reg_t) : Prop :=
      latest_write (update_function st log) reg = latest_write log reg.

  End LogHelpers.


  Section CoreAxioms.
    (* TODO: rf *)
    Definition internal_reg_reset (st: state) (reg: internal_reg_t) : Prop :=
      ContextEnv.(getenv) st (internal reg) = r (internal reg).

    Definition reg_reset (st: state) (reg: reg_t) : Prop :=
      match reg with
      | pc => True (* don't care *)
      | purge => True (* don't care *)
      | internal s => internal_reg_reset st s
      | _ => ContextEnv.(getenv) st reg = r reg
      end.

    Definition valid_reset_state (st: state) : Prop :=
      forall reg, reg_reset st reg.

    (* If in Ready/Purged state, not allowed to write to purge *)
    Inductive purge_state_machine (st: state) (log: Log R ContextEnv): Prop :=
    | PurgeRestart :
        forall (purge_state_eq: ContextEnv.(getenv) st purge = ENUM_purge_restart)
          (no_writes_or_write_ready: 
             update_no_writes_to_reg st log purge \/
             latest_write (update_function st log) purge = Some ENUM_purge_ready),
          purge_state_machine st log
    | PurgeReady :
        forall (purge_state_eq: ContextEnv.(getenv) st purge = ENUM_purge_ready)
          (no_writes: update_no_writes_to_reg st log purge),
          purge_state_machine st log
    | PurgePurging :
        forall (purge_state_eq: ContextEnv.(getenv) st purge = ENUM_purge_purging)
          (no_writes_or_write_purged: 
             update_no_writes_to_reg st log purge \/
             latest_write (update_function st log) purge = Some ENUM_purge_purged
          ),
          purge_state_machine st log
    | PurgePurged :
        forall (purge_state_eq: ContextEnv.(getenv) st purge = ENUM_purge_purged)
          (no_writes_to_any_reg: forall reg, update_no_writes_to_reg st log reg),
          purge_state_machine st log
    .

    Definition valid_core_id (st: state) : Prop :=
      ContextEnv.(getenv) st core_id = r core_id.

    Definition valid_state_by_purge (st: state) : Prop :=
      ContextEnv.(getenv) st purge = ENUM_purge_restart \/
      ContextEnv.(getenv) st purge = ENUM_purge_purged ->
      valid_reset_state st.

    Axiom valid_internal_state : state -> Prop.

    Definition valid_input_log (log: Log R ContextEnv) :=
      log = empty_log.

    Definition valid_state (st: state) : Prop :=
      valid_core_id st /\
      valid_state_by_purge st /\
      valid_internal_state st.

    Axiom valid_state_preserved: 
      forall (st: state) (log: Log R ContextEnv),
      valid_state st ->
      valid_input_log log ->
      valid_state (commit_update st (update_function st log)).

    (* TODO: and valid_state_preserved after external world effects on FIFO? *)

    (* Core_id is unchanged *)
    Axiom core_id_unchanged : 
      forall (st: state) (log: Log R ContextEnv),
      latest_write (update_function st log) core_id = latest_write log core_id.

    Axiom valid_purge_state_machine :
      forall (st: state) (log: Log R ContextEnv),
        purge_state_machine st log.

    (* If we are in a valid state and write Purging->Purged, then we promise to be in a reset state.
     * This is a stronger statement that we ultimately need, but is easier to phrase/work with.
     * I think with modules (/being written in a more modular way without register sharing) this will be easier.
     *)
    Axiom write_purged_impl_in_reset_state :
      forall (st: state) (log: Log R ContextEnv),
      latest_write (update_function st log) purge = Some ENUM_purge_purged ->
      latest_write log purge <> Some ENUM_purge_purged ->
      valid_reset_state (commit_update st (update_function st log)).

    (*
    | ValidSt_Restart :
        forall (purge_state_eq: ContextEnv.(getenv) st purge = ENUM_purge_restart)
          (reset_st: valid_reset_state st),
        valid_state st
    | ValidSt_Ready :
        forall (purge_state_eq: ContextEnv.(getenv) st purge = ENUM_purge_ready),
        valid_state st
    | ValidSt_Purging :
        forall (purge_state_eq: ContextEnv.(getenv) st purge = ENUM_purge_purging),
        valid_state st
    | ValidSt_Purged :
        forall (purge_state_eq: ContextEnv.(getenv) st purge = ENUM_purge_purged)
          (reset_st: valid_reset_state st),
        valid_state st.
    *)

  End CoreAxioms.

End Core_sig.

Module EnclaveInterface.
  Import Common.

  Definition enclave_data :=
    {| struct_name := "enclave_data";
       struct_fields := [("eid", bits_t 32);
                         ("addr_min", bits_t 32);
                         ("size", bits_t 32);
                         ("valid", bits_t 1)
                        ]
    |}.

  Record struct_enclave_data :=
    { enclave_data_eid : bits_t 32;
      enclave_data_addr_min : bits_t 32;
      enclave_data_size : bits_t 32;
      enclave_data_valid : bits_t 1;
    }.

  Definition mk_enclave_data (data: struct_enclave_data) : struct_t enclave_data :=
    (data.(enclave_data_eid),
     (data.(enclave_data_addr_min), (data.(enclave_data_size), (data.(enclave_data_valid), tt)))).

  (* TODO: generalize this. *)
  Definition extract_enclave_data (data: struct_t enclave_data) : struct_enclave_data :=
      let '(eid, (addr_min, (size, (valid, _)))) := data in
      {| enclave_data_eid := eid;
         enclave_data_addr_min := addr_min;
         enclave_data_size := size;
         enclave_data_valid := valid;
      |}.

  Definition bits_id_to_ind_id (eid: bits_t 32) : option enclave_id :=
    match Bits.to_nat eid with
    | 0 => Some Enclave0
    | 1 => Some Enclave1
    | 2 => Some Enclave2
    | 3 => Some Enclave3
    | _ => None
    end.

  Definition enclave_id_to_bits (eid: enclave_id) : bits_t 32 :=
    match eid with
    | Enclave0 => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    | Enclave1 => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1
    | Enclave2 => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0
    | Enclave3 => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1
    end.

End EnclaveInterface.

Module SecurityMonitor (External: External_sig) (Params: EnclaveParameters).
  Import Common.
  Import EnclaveInterface.

  Inductive internal_reg_t' :=
  | limbo0
  | limbo1
  | enc_data0
  | enc_data1
  .

  Definition internal_reg_t := internal_reg_t'.

  Definition R_internal (idx: internal_reg_t) : type :=
    match idx with
    | limbo0 => bits_t 1
    | limbo1 => bits_t 1
    | enc_data0 => struct_t enclave_data
    | enc_data1 => struct_t enclave_data
    end.

  Definition r_internal (idx: internal_reg_t) : R_internal idx :=
    match idx with
    | limbo0 => Bits.zero
    | limbo1 => Bits.zero
    | enc_data0 => let eid := Bits.zero in
                  let addr_min := Params.enclave_base Enclave0 in
                  let size := Params.enclave_size Enclave0 in
                  let valid := Ob~1 in
                  ((eid, (addr_min, (size, (valid, tt)))))
    | einc_data1 => let eid := Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1 in
                   let addr_min := Params.enclave_base Enclave1 in
                   let size := Params.enclave_size Enclave1 in
                   let valid := Ob~1 in
                   ((eid, (addr_min, (size, (valid, tt)))))
    end.

  Instance FiniteType_internal_reg_t : FiniteType internal_reg_t := _.

  Inductive reg_t' : Type :=
  | fromCore0_IMem (state: MemReq.reg_t)
  | fromCore0_DMem (state: MemReq.reg_t)
  | fromCore0_Enc (state: EnclaveReq.reg_t)
  | toCore0_IMem (state: MemResp.reg_t)
  | toCore0_DMem (state: MemResp.reg_t)
  (* Core1 <-> SM *)
  | fromCore1_IMem (state: MemReq.reg_t)
  | fromCore1_DMem (state: MemReq.reg_t)
  | fromCore1_Enc (state: EnclaveReq.reg_t)
  | toCore1_IMem (state: MemResp.reg_t)
  | toCore1_DMem (state: MemResp.reg_t)
  (* SM <-> Mem *)
  | toMem0_IMem (state: MemReq.reg_t)
  | toMem0_DMem (state: MemReq.reg_t)
  | toMem1_IMem (state: MemReq.reg_t)
  | toMem1_DMem (state: MemReq.reg_t)
  | fromMem0_IMem (state: MemResp.reg_t)
  | fromMem0_DMem (state: MemResp.reg_t)
  | fromMem1_IMem (state: MemResp.reg_t)
  | fromMem1_DMem (state: MemResp.reg_t)
  | pc_core0
  | pc_core1
  | purge_core0
  | purge_core1
  | purge_mem0
  | purge_mem1
  | internal (idx: internal_reg_t)
  .

  Definition reg_t : Type := reg_t'.

  Definition R (idx: reg_t) :=
    match idx with
    | fromCore0_IMem st => MemReq.R st
    | fromCore0_DMem st => MemReq.R st
    | fromCore0_Enc st => EnclaveReq.R st
    | toCore0_IMem st => MemResp.R st
    | toCore0_DMem st => MemResp.R st
    (* Core1 <-> SM *)
    | fromCore1_IMem st => MemReq.R st
    | fromCore1_DMem st => MemReq.R st
    | fromCore1_Enc st => EnclaveReq.R st
    | toCore1_IMem st => MemResp.R st
    | toCore1_DMem st => MemResp.R st
    (* SM <-> Mem *)
    | toMem0_IMem st => MemReq.R st
    | toMem0_DMem st => MemReq.R st
    | toMem1_IMem st => MemReq.R st
    | toMem1_DMem st => MemReq.R st
    | fromMem0_IMem st => MemResp.R st
    | fromMem0_DMem st => MemResp.R st
    | fromMem1_IMem st => MemResp.R st
    | fromMem1_DMem st => MemResp.R st
    | pc_core0 => bits_t 32
    | pc_core1 => bits_t 32
    | purge_core0 => enum_t purge_state
    | purge_core1 => enum_t purge_state
    | purge_mem0 => enum_t purge_state
    | purge_mem1 => enum_t purge_state
    | internal st => R_internal st
    end.

  Definition r (idx: reg_t) : R idx :=
    match idx with
    | fromCore0_IMem st => MemReq.r st
    | fromCore0_DMem st => MemReq.r st
    | fromCore0_Enc st => EnclaveReq.r st
    | toCore0_IMem st => MemResp.r st
    | toCore0_DMem st => MemResp.r st
    (* Core1 <-> SM *)
    | fromCore1_IMem st => MemReq.r st
    | fromCore1_DMem st => MemReq.r st
    | fromCore1_Enc st => EnclaveReq.r st
    | toCore1_IMem st => MemResp.r st
    | toCore1_DMem st => MemResp.r st
    (* SM <-> Mem *)
    | toMem0_IMem st => MemReq.r st
    | toMem0_DMem st => MemReq.r st
    | toMem1_IMem st => MemReq.r st
    | toMem1_DMem st => MemReq.r st
    | fromMem0_IMem st => MemResp.r st
    | fromMem0_DMem st => MemResp.r st
    | fromMem1_IMem st => MemResp.r st
    | fromMem1_DMem st => MemResp.r st
    | pc_core0 => Bits.zero
    | pc_core1 => Bits.zero
    | purge_core0 => value_of_bits (Bits.zero)
    | purge_core1 => value_of_bits (Bits.zero)
    | purge_mem0 => value_of_bits (Bits.zero)
    | purge_mem1 => value_of_bits (Bits.zero)
    | internal st => r_internal st
    end.

  Instance FiniteType_reg_t : FiniteType reg_t := _.

  Definition Sigma := External.Sigma.
  Definition ext_fn_t := External.ext_fn_t.
  Definition state := env_t ContextEnv (fun idx : reg_t => R idx).

  Definition eid_to_initial_enclave_data (eid: enclave_id) : struct_t enclave_data :=
    mk_enclave_data {| enclave_data_eid := enclave_id_to_bits eid;
                       enclave_data_addr_min := Params.enclave_base eid;
                       enclave_data_size := Params.enclave_size eid;
                       enclave_data_valid := Ob~1
                    |}.

  (* TODO: use the above here *)
  Definition eid_to_enc_data : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun eid_to_enc_data (eid: bits_t 32) : struct_t enclave_data =>
         match eid with
         | #Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0 =>
             struct enclave_data { eid := eid;
                                   addr_min := (#(Params.enclave_base Enclave0));
                                   size := (#(Params.enclave_size Enclave0));
                                   valid := Ob~1
                                 }
         | #Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1 =>
             struct enclave_data { eid := eid;
                                   addr_min := (#(Params.enclave_base Enclave1));
                                   size := (#(Params.enclave_size Enclave1));
                                   valid := Ob~1
                                 }
         | #Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0 =>
             struct enclave_data { eid := eid;
                                   addr_min := (#(Params.enclave_base Enclave2));
                                   size := (#(Params.enclave_size Enclave2));
                                   valid := Ob~1
                                 }
         | #Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1 =>
             struct enclave_data { eid := eid;
                                   addr_min := (#(Params.enclave_base Enclave3));
                                   size := (#(Params.enclave_size Enclave3));
                                   valid := Ob~1
                                 }
         return default : `UConst (tau := struct_t enclave_data) (value_of_bits (Bits.zero))`
         end
    }}.

  Definition lookup_reg_limbo (core: ind_core_id) : reg_t :=
    match core with
    | CoreId0 => internal limbo0
    | CoreId1 => internal limbo1
    end.

  Definition lookup_reg_enc_data (core: ind_core_id) : reg_t :=
    match core with
    | CoreId0 => internal enc_data0
    | CoreId1 => internal enc_data1
    end.

  Definition lookup_reg_proc_reset (core: ind_core_id) : reg_t :=
    match core with
    | CoreId0 => purge_core0
    | CoreId1 => purge_core1
    end.

  Definition lookup_reg_mem_reset (core: ind_core_id) : reg_t :=
    match core with
    | CoreId0 => purge_mem0
    | CoreId1 => purge_mem1
    end.

  Definition lookup_reg_pc (core: ind_core_id) : reg_t :=
    match core with
    | CoreId0 => pc_core0
    | CoreId1 => pc_core1
    end.

  (* TODO: This is wrong. While in a limbo state, other core can't switch into old enclave until done reset *)
  Definition canSwitchToEnc (core: ind_core_id) : UInternalFunction reg_t empty_ext_fn_t :=
    let other_core := match core with CoreId0 => CoreId1 | CoreId1 => CoreId0 end in
    let reg_other_enc := lookup_reg_enc_data other_core in
    {{ fun canSwitchToEnc (eid: bits_t 32) : bits_t 1 =>
         let other_enc_data := read0(reg_other_enc) in
         get(other_enc_data, eid) != eid
    }}.


  (* TODO: currently another core can switch into the same enclave *)
  (* TODO: as written, order matters and there's interference.
     We should combine the rule so that order doesn't matter *)
  Definition sm_update_enclave (core: ind_core_id) : uaction reg_t ext_fn_t :=
    let reg_limbo := lookup_reg_limbo core in
    let reg_enc := lookup_reg_enc_data core in
    let fromCore :=
        match core with
        | CoreId0 => fromCore0_Enc
        | CoreId1 => fromCore1_Enc
        end in
    {{ when (!read0(reg_limbo)) do (
         let max_eid := |32`d3| in
         let enclaveRequest := fromCore.(EnclaveReq.deq)() in
         let eid := get(enclaveRequest, eid) in
         let can_switch_to_eid := {canSwitchToEnc core}(eid) in
         if (eid <= max_eid && can_switch_to_eid ) then
           write0(reg_enc, eid_to_enc_data(eid));
           write0(reg_limbo, Ob~1)
         else (* drop it *)
           pass
       )
    }}.

  Definition MMIO_UART_ADDRESS := Ob~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0.

  Definition sm_filter_reqs (core: ind_core_id) (cache: ind_cache_type) : uaction reg_t ext_fn_t :=
    let reg_limbo := lookup_reg_limbo core in
    let reg_enc := lookup_reg_enc_data core in
    let '(fromCore, toMem) :=
        match core, cache with
        | CoreId0, CacheType_Imem => (fromCore0_IMem, toMem0_IMem)
        | CoreId0, CacheType_Dmem => (fromCore0_DMem, toMem0_DMem)
        | CoreId1, CacheType_Imem => (fromCore1_IMem, toMem1_IMem)
        | CoreId1, CacheType_Dmem => (fromCore1_DMem, toMem1_DMem)
        end in
    {{ when (!read0(reg_limbo)) do
         let request := fromCore.(MemReq.deq)() in
         let address := get(request, addr) in
         let enc_data := read0(reg_enc) in
         let addr_min := get(enc_data, addr_min) in
         let addr_max := get(enc_data, size) + addr_min in
         let TODO_temp_bypass := address >= #(MMIO_UART_ADDRESS) in
         if ((addr_min <= address && address < addr_max) ||  TODO_temp_bypass) then
           toMem.(MemReq.enq)(request)
         else pass
    }}.

  Definition sm_filter_resps (core: ind_core_id) (cache: ind_cache_type) : uaction reg_t ext_fn_t :=
    let reg_limbo := lookup_reg_limbo core in
    let reg_enc := lookup_reg_enc_data core in
    let '(fromMem, toCore) :=
        match core, cache with
        | CoreId0, CacheType_Imem => (fromMem0_IMem, toCore0_IMem)
        | CoreId0, CacheType_Dmem => (fromMem0_DMem, toCore0_DMem)
        | CoreId1, CacheType_Imem => (fromMem1_IMem, toCore1_IMem)
        | CoreId1, CacheType_Dmem => (fromMem1_DMem, toCore1_DMem)
        end in
    {{ when (!read0(reg_limbo)) do
         let response:= fromMem.(MemResp.deq)() in
         let address := get(response, addr) in
         let enc_data := read0(reg_enc) in
         let addr_min := get(enc_data, addr_min) in
         let addr_max := get(enc_data, size) + addr_min in
         let TODO_temp_bypass := address >= #(MMIO_UART_ADDRESS) in
         if (addr_min <= address && address < addr_max) || TODO_temp_bypass then
           toCore.(MemResp.enq)(response)
         else pass
    }}.

  Definition sm_reset_processor_and_memory (core: ind_core_id): uaction reg_t ext_fn_t :=
    let reg_limbo := lookup_reg_limbo core in
    let reg_proc_reset := lookup_reg_proc_reset core in
    let reg_mem_reset := lookup_reg_mem_reset core in
    {{ (if (read0(reg_limbo) && read0(reg_proc_reset) == enum purge_state { Ready }) then
         write0(reg_proc_reset, enum purge_state { Purging })
        else pass);
       if (read0(reg_limbo) && read0(reg_mem_reset) == enum purge_state { Ready }) then
         write0(reg_mem_reset, enum purge_state { Purging })
       else pass
    }}.

  Definition eid_to_bootloader_addr : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun eid_to_bootloader_addr (eid: bits_t 32) : bits_t 32 =>
         match eid with
         | #Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0 =>
             #(Params.enclave_bootloader_addr Enclave0)
         | #Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1 =>
             #(Params.enclave_bootloader_addr Enclave1)
         | #Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0 =>
             #(Params.enclave_bootloader_addr Enclave2)
         | #Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1 =>
             #(Params.enclave_bootloader_addr Enclave3)
         return default : |32`d0|
         end
    }}.
  Definition reset_fifos : UInternalFunction reg_t ext_fn_t :=
    {{ fun reset_fifos () : bits_t 0 =>
         fromCore0_IMem.(MemReq.reset)();
         fromCore0_DMem.(MemReq.reset)();
         fromCore0_Enc.(EnclaveReq.reset)();
         toCore0_IMem.(MemResp.reset)();
         toCore0_DMem.(MemResp.reset)();
         fromCore1_IMem.(MemReq.reset)();
         fromCore1_DMem.(MemReq.reset)();
         fromCore1_Enc.(EnclaveReq.reset)();
         toCore1_IMem.(MemResp.reset)();
         toCore1_DMem.(MemResp.reset)();
         toMem0_IMem.(MemReq.reset)();
         toMem0_DMem.(MemReq.reset)();
         toMem1_IMem.(MemReq.reset)();
         toMem1_DMem.(MemReq.reset)();
         fromMem0_IMem.(MemResp.reset)();
         fromMem0_DMem.(MemResp.reset)();
         fromMem1_IMem.(MemResp.reset)();
         fromMem1_DMem.(MemResp.reset)()
    }}.


  Definition sm_restart_pipeline (core: ind_core_id) : uaction reg_t ext_fn_t :=
    let reg_limbo := lookup_reg_limbo core in
    let reg_enc := lookup_reg_enc_data core in
    let reg_proc_reset := lookup_reg_proc_reset core in
    let reg_mem_reset := lookup_reg_mem_reset core in
    let reg_pc := lookup_reg_pc core in
    {{ if (read0(reg_limbo) && read0(reg_proc_reset) == enum purge_state { Purged } &&
           read0(reg_mem_reset) == enum purge_state { Purged }) then
         (* Do resets *)
         reset_fifos();
         (* Restart *)
         write0(reg_limbo, Ob~0);
         write0(reg_proc_reset, enum purge_state { Restart });
         write0(reg_mem_reset, enum purge_state { Restart });
         let enc_data := read0(reg_enc) in
         let max_eid := |32`d3| in
         let eid := get(enc_data,eid) in
         if (eid <= max_eid) then
           write0(reg_pc, eid_to_bootloader_addr(eid))
         else
           fail
       else fail
    }}.

  Definition tc_update_enclave0 := tc_rule R Sigma (sm_update_enclave CoreId0) <: rule R Sigma.
  Definition tc_update_enclave1 := tc_rule R Sigma (sm_update_enclave CoreId1) <: rule R Sigma.

  Definition tc_filter_reqs_imem0 := tc_rule R Sigma (sm_filter_reqs CoreId0 CacheType_Imem) <: rule R Sigma.
  Definition tc_filter_reqs_dmem0 := tc_rule R Sigma (sm_filter_reqs CoreId0 CacheType_Dmem) <: rule R Sigma.
  Definition tc_filter_reqs_imem1 := tc_rule R Sigma (sm_filter_reqs CoreId1 CacheType_Imem) <: rule R Sigma.
  Definition tc_filter_reqs_dmem1 := tc_rule R Sigma (sm_filter_reqs CoreId1 CacheType_Dmem) <: rule R Sigma.

  Definition tc_filter_resps_imem0 := tc_rule R Sigma (sm_filter_resps CoreId0 CacheType_Imem) <: rule R Sigma.
  Definition tc_filter_resps_dmem0 := tc_rule R Sigma (sm_filter_resps CoreId0 CacheType_Dmem) <: rule R Sigma.
  Definition tc_filter_resps_imem1 := tc_rule R Sigma (sm_filter_resps CoreId1 CacheType_Imem) <: rule R Sigma.
  Definition tc_filter_resps_dmem1 := tc_rule R Sigma (sm_filter_resps CoreId1 CacheType_Dmem) <: rule R Sigma.

  Definition tc_reset_proc_and_mem0 := tc_rule R Sigma (sm_reset_processor_and_memory CoreId0) <: rule R Sigma.
  Definition tc_reset_proc_and_mem1 := tc_rule R Sigma (sm_reset_processor_and_memory CoreId1) <: rule R Sigma.

  Definition tc_restart_pipeline0 := tc_rule R Sigma (sm_restart_pipeline CoreId0) <: rule R Sigma.
  Definition tc_restart_pipeline1 := tc_rule R Sigma (sm_restart_pipeline CoreId1) <: rule R Sigma.

  (* Definition tc_forward := tc_rule R Sigma forward <: rule R Sigma. *)

  Inductive rule_name_t' :=
  | UpdateEnclave0
  | UpdateEnclave1
  | FilterReqsIMem0
  | FilterReqsDMem0
  | FilterReqsIMem1
  | FilterReqsDMem1
  | FilterRespsIMem0
  | FilterRespsDMem0
  | FilterRespsIMem1
  | FilterRespsDMem1
  | ResetProcAndMem0
  | ResetProcAndMem1
  | RestartPipeline0
  | RestartPipeline1
  .

  Definition rule_name_t := rule_name_t'.

  Definition rules (rl : rule_name_t) : rule R Sigma :=
    match rl with
    | UpdateEnclave0 => tc_update_enclave0
    | UpdateEnclave1 => tc_update_enclave1
    | FilterReqsIMem0 => tc_filter_reqs_imem0
    | FilterReqsDMem0 => tc_filter_reqs_dmem0
    | FilterReqsIMem1 => tc_filter_reqs_imem1
    | FilterReqsDMem1 => tc_filter_reqs_dmem1
    | FilterRespsIMem0 => tc_filter_resps_imem0
    | FilterRespsDMem0 => tc_filter_resps_dmem0
    | FilterRespsIMem1 => tc_filter_resps_imem1
    | FilterRespsDMem1 => tc_filter_resps_dmem1
    | ResetProcAndMem0 => tc_reset_proc_and_mem0
    | ResetProcAndMem1 => tc_reset_proc_and_mem1
    | RestartPipeline0 => tc_restart_pipeline0
    | RestartPipeline1 => tc_restart_pipeline1
    end.

  Definition schedule : Syntax.scheduler pos_t rule_name_t :=
    UpdateEnclave0 |> UpdateEnclave1
                   |> FilterReqsIMem0 |> FilterReqsDMem0 |> FilterReqsIMem1 |> FilterReqsDMem1
                   |> FilterRespsIMem0 |> FilterRespsDMem0 |> FilterRespsIMem1 |> FilterRespsDMem1
                   |> ResetProcAndMem0 |> ResetProcAndMem1
                   |> RestartPipeline0 |> RestartPipeline1
                   |> done.

  Section Semantics.
    Definition empty_log : Log R ContextEnv := log_empty.
    Parameter update_function : state -> Log R ContextEnv -> Log R ContextEnv.
      (* interp_scheduler' st ? rules log scheduler. *)

  End Semantics.

  Section LogHelpers.
    Definition update_no_writes_to_reg (st: state) (log: Log R ContextEnv) (reg: reg_t) : Prop :=
      latest_write (update_function st log) reg = latest_write log reg.

  End LogHelpers.

  Section ValidInput.
    Definition valid_input_log (log: Log R ContextEnv) : Prop. Admitted.
    Definition valid_input_state (st: state) : Prop. Admitted.
    Definition valid_feedback_log : state -> Log R ContextEnv -> Log R ContextEnv -> Prop. Admitted.

    Definition internal_reg_to_taint (reg: internal_reg_t) : option ind_core_id :=
      match reg with
      | limbo0 => Some CoreId0
      | limbo1 => Some CoreId1
      | enc_data0 => Some CoreId0 
      | enc_data1 => Some CoreId1
      end.

    Definition reg_to_taint (reg: reg_t) : option ind_core_id :=
      match reg with
      | fromCore0_IMem st => Some CoreId0
      | fromCore0_DMem st => Some CoreId0
      | fromCore0_Enc st => Some CoreId0 
      | toCore0_IMem st => Some CoreId0
      | toCore0_DMem st => Some CoreId0
      (* Core1 <-> SM *)
      | fromCore1_IMem st => Some CoreId1
      | fromCore1_DMem st => Some CoreId1
      | fromCore1_Enc st => Some CoreId1
      | toCore1_IMem st => Some CoreId1
      | toCore1_DMem st => Some CoreId1
      (* SM <-> Mem *)
      | toMem0_IMem st => Some CoreId0
      | toMem0_DMem st => Some CoreId0
      | toMem1_IMem st => Some CoreId1
      | toMem1_DMem st => Some CoreId1
      | fromMem0_IMem st => Some CoreId0
      | fromMem0_DMem st => Some CoreId0
      | fromMem1_IMem st => Some CoreId1
      | fromMem1_DMem st => Some CoreId1
      | pc_core0 => Some CoreId0
      | pc_core1 => Some CoreId1
      | purge_core0 => Some CoreId0
      | purge_core1 => Some CoreId1
      | purge_mem0 => Some CoreId0
      | purge_mem1 => Some CoreId1
      | internal st => internal_reg_to_taint st
    end.
 
  End ValidInput.

  Section Initialise.

    Definition initialise_internal_with_eid
               (eid0: option enclave_id) (eid1: option enclave_id) (idx: internal_reg_t) : R_internal idx :=
      match idx with
      | limbo0 => Ob~0
      | limbo1 => Ob~0
      | enc_data0 =>
         match eid0 with
         | Some id => eid_to_initial_enclave_data id
         | None => value_of_bits (Bits.zero)
         end
      | enc_data1 =>
         match eid1 with
         | Some id => eid_to_initial_enclave_data id
         | None => value_of_bits (Bits.zero)
         end
      end.

    Definition initialise_with_eid (eid0: option enclave_id) (eid1: option enclave_id) (idx: reg_t) : R idx :=
      match idx with
      | internal s => initialise_internal_with_eid eid0 eid1 s
      | s => r s
      end.

  End Initialise.

  Section ValidResetState.

    (* TODO: not quite complete. *)
    Definition valid_reset_state (st: state) (core_id: ind_core_id) (eid: enclave_id): Prop :=
      forall reg, reg_to_taint reg = Some core_id ->
             (reg <> pc_core0 /\ reg <> pc_core1) ->
             match core_id with
             | CoreId0 => initialise_with_eid (Some eid) None reg = ContextEnv.(getenv) st reg
             | CoreId1 => initialise_with_eid None (Some eid) reg = ContextEnv.(getenv) st reg
             end.

  End ValidResetState.

  Section SMInternalAxioms.

    Definition valid_enclave_data (data: struct_t enclave_data) : Prop :=
      let enclave_data := extract_enclave_data data in
      match bits_id_to_ind_id enclave_data.(enclave_data_eid) with
      | Some id =>
          enclave_data.(enclave_data_addr_min) = Params.enclave_base id /\
          enclave_data.(enclave_data_size) = Params.enclave_size id
      | None => False
      end.

    Definition valid_enclave_data_regs (st: state) : Prop :=
      valid_enclave_data (ContextEnv.(getenv) st (internal enc_data0)) /\
      valid_enclave_data (ContextEnv.(getenv) st (internal enc_data1)).

    (* TODO: incomplete *)
    Definition valid_internal_state (st: state) : Prop :=
      valid_enclave_data_regs st.

    Definition limbo_eq (st: state) (core_id: ind_core_id) (v: bits_t 1): Prop :=
      match core_id with
      | CoreId0 => ContextEnv.(getenv) st (internal limbo0) = v
      | CoreId1 => ContextEnv.(getenv) st (internal limbo1) = v
      end.

    (* Idea:
     * - ghost state tracks when cores are done purging and when cores have restarted? 
     * - or we explicitly add it to the observations! <-- This seems better, since it defines what we care about
     *)

    Definition equiv_log_at_core (core_id: ind_core_id) (log1: Log R ContextEnv) (log2: Log R ContextEnv) : Prop :=
      forall r, reg_to_taint r = Some core_id ->
           ContextEnv.(getenv) log1 r = ContextEnv.(getenv) log2 r.
        
    Definition equiv_log_at_shared (log1: Log R ContextEnv) (log2: Log R ContextEnv) : Prop :=
      forall r, reg_to_taint r = None ->
           ContextEnv.(getenv) log1 r = ContextEnv.(getenv) log2 r.

    Definition equiv_log_for_core (core_id: ind_core_id) (log1: Log R ContextEnv) (log2: Log R ContextEnv) : Prop :=
      equiv_log_at_core core_id log1 log2 /\ equiv_log_at_shared log1 log2.

    Definition equiv_st_at_core (core_id: ind_core_id) (st1: state) (st2: state) : Prop :=
      forall r, reg_to_taint r = Some core_id ->
           ContextEnv.(getenv) st1 r = ContextEnv.(getenv) st2 r.
        
    Definition equiv_st_at_shared (st1: state) (st2: state) : Prop :=
      forall r, reg_to_taint r = None ->
           ContextEnv.(getenv) st1 r = ContextEnv.(getenv) st2 r.

    Definition equiv_st_for_core (core_id: ind_core_id) (st1: state) (st2: state) : Prop :=
      equiv_st_at_core core_id st1 st2 /\ equiv_st_at_shared st1 st2.

    (* Assuming we are not initially in a limbo state, output is a function only of taint0 registers *)
    Definition output_is_a_function_of_partitioned_registers:
      forall (core_id: ind_core_id) (st0 st1: state) (log0 log1: Log R ContextEnv),
      limbo_eq st0 core_id Ob~0 ->
      valid_input_state st0 ->
      valid_input_state st1 ->
      valid_input_log log0 ->
      valid_input_log log1 ->
      equiv_st_for_core core_id st0 st1 ->
      equiv_log_for_core core_id log0 log1 ->
      equiv_log_for_core core_id (update_function st0 log0) (update_function st1 log1).
    Admitted.
   
    (* TODO: figure out dependent types *)
    Definition no_enq_to_output_reg (core_id: ind_core_id) (reg: reg_t) (log: Log R ContextEnv): Prop :=
      match reg with
      | toCore0_IMem MemResp.valid0 =>
          core_id = CoreId0 /\
          latest_write log (toCore0_IMem MemResp.valid0) <> Some Ob~1
      | toCore0_DMem MemResp.valid0 =>
          core_id = CoreId0 /\
          latest_write log (toCore0_DMem MemResp.valid0) <> Some Ob~1
      | toMem0_IMem MemReq.valid0 =>
          core_id = CoreId0 /\
          latest_write log (toMem0_IMem MemReq.valid0) <> Some Ob~1
      | toMem0_DMem MemReq.valid0 =>
          core_id = CoreId0 /\
          latest_write log (toMem0_DMem MemReq.valid0) <> Some Ob~1
      | toCore1_IMem MemResp.valid0 =>
          core_id = CoreId1 /\
          latest_write log (toCore1_IMem MemResp.valid0) <> Some Ob~1
      | toCore1_DMem MemResp.valid0 =>
          core_id = CoreId1 /\
          latest_write log (toCore1_DMem MemResp.valid0) <> Some Ob~1
      | toMem1_IMem MemReq.valid0 =>
          core_id = CoreId1 /\
          latest_write log (toMem1_IMem MemReq.valid0) <> Some Ob~1
      |toMem1_DMem MemReq.valid0 =>
          core_id = CoreId1 /\
          latest_write log (toMem1_DMem MemReq.valid0) <> Some Ob~1
      | _ => False
      end.

    (* TODO: rephrase this. This is annoying to work with *)
    Definition no_external_enqs (core_id: ind_core_id) (st: state) (log: Log R ContextEnv) : Prop :=
      forall reg, no_enq_to_output_reg core_id reg (update_function st log) \/
             update_no_writes_to_reg st log reg.

    (* If the core starts out in a limbo state, we say there are no valid writes to the outside world *)
    Definition limbo_implies_no_external_enqs:
      forall (core_id: ind_core_id) (st: state) (log: Log R ContextEnv),
      limbo_eq st core_id Ob~1 ->
      valid_input_state st ->
      valid_input_log log ->
      no_external_enqs core_id st log.
    Proof.
    Admitted.
  End SMInternalAxioms.

  (* TODO: this needs to be in a framework *)
  Section CycleModel.
    Variable input_fn : state -> Log R ContextEnv.
    Variable pf_input_fn_generates_valid_log : forall (st: state), valid_input_log (input_fn st).
    Variable feedback_fn : state -> Log R ContextEnv -> Log R ContextEnv.
    Variable pf_feedback_fn_generates_valid_og
      : forall (st: state) (log: Log R ContextEnv), valid_feedback_log st log (feedback_fn st log).

    Definition do_step (st: state) : state :=
      let input := input_fn st in
      let update := update_function st input in
      let final := feedback_fn st update in
      commit_update st final.

    (* Model cycle with input, schedule, post-schedule update
     * Important points
     * - From a reset state, requests to memory are a function only of inputs to relevant core,
     *   until a context switch is requested
     * - All requests to memory are within range of the enclave
     * - When a context switch is requested, we have no more requests to memory
     * - Need something about how the time it takes for memory/core to reset is independent...,
     *   but that's not here
     *)

    Definition prop_holds_about_sm_step (st: state) (P: state -> Log R ContextEnv -> Log R ContextEnv -> Prop) : Prop :=
      let input := input_fn st in
      let update := update_function st input in
      P st input update.

    Fixpoint prop_holds_for_n_sm_steps (n: nat) (st: state) (P: state -> Log R ContextEnv -> Log R ContextEnv -> Prop) : Prop :=
      match n with
      | 0 => True
      | S n' =>
        let state' := do_step st in
        prop_holds_about_sm_step st P /\
        prop_holds_for_n_sm_steps n' state' P
      end.

    Definition P_partition (core_id: ind_core_id)
               (st: state) (input_log: Log R ContextEnv) (output_log: Log R ContextEnv) : Prop :=
      forall st' log',
      valid_input_state st' ->
      valid_input_log log' ->
      equiv_st_for_core core_id st st' ->
      equiv_log_for_core core_id input_log log' ->
      equiv_log_for_core core_id output_log (update_function st' log').

    (* TODO: restructure *)
    Definition observe_enclave_reqs (log: Log R ContextEnv) (core_id: ind_core_id) : option (struct_t enclave_req).
    Admitted.

    Definition valid_enclave_req (req: struct_t enclave_req) : Prop :=
      let '(eid, _) := req in
      Bits.to_nat eid < 4.

    Definition P_no_enclave_req (core_id: ind_core_id): state -> Log R ContextEnv -> Log R ContextEnv -> Prop :=
      fun st input_log output_log =>
        match observe_enclave_reqs output_log core_id with
        | None => True
        | Some req => valid_enclave_req req
        end.

    (* TODO: stop duplicating code *)
    Definition observe_imem_reqs_to_mem0 (log: Log R ContextEnv) : option (struct_t mem_req) :=
      match latest_write0 log (toMem0_IMem MemReq.valid0) with
      | Some b =>
          if Bits.single b then (latest_write0 log (toMem0_IMem MemReq.data0)) else None
      | None => None
      end.

    Definition observe_imem_reqs_to_mem1 (log: Log R ContextEnv) : option (struct_t mem_req) :=
      match latest_write0 log (toMem1_IMem MemReq.valid0) with
      | Some b =>
          if Bits.single b then (latest_write0 log (toMem1_IMem MemReq.data0)) else None
      | None => None
      end.

    Definition observe_imem_reqs_to_mem (log: Log R ContextEnv) (core_id: ind_core_id) : option (struct_t mem_req) :=
      match core_id with
      | CoreId0 => observe_imem_reqs_to_mem0 log
      | CoreId1 => observe_imem_reqs_to_mem1 log
      end.

    Definition observe_dmem_reqs_to_mem0 (log: Log R ContextEnv) : option (struct_t mem_req) :=
      match latest_write0 log (toMem0_DMem MemReq.valid0) with
      | Some b =>
          if Bits.single b then (latest_write0 log (toMem0_DMem MemReq.data0)) else None
      | None => None
      end.

    Definition observe_dmem_reqs_to_mem1 (log: Log R ContextEnv) : option (struct_t mem_req) :=
      match latest_write0 log (toMem1_DMem MemReq.valid0) with
      | Some b =>
          if Bits.single b then (latest_write0 log (toMem1_DMem MemReq.data0)) else None
      | None => None
      end.

    Definition observe_dmem_reqs_to_mem (log: Log R ContextEnv) (core_id: ind_core_id) : option (struct_t mem_req) :=
      match core_id with
      | CoreId0 => observe_dmem_reqs_to_mem0 log
      | CoreId1 => observe_dmem_reqs_to_mem1 log
      end.

    Definition P_mem_reqs_in_range (mem: ind_cache_type) (core_id: ind_core_id) (eid: enclave_id)
                                   : state -> Log R ContextEnv -> Log R ContextEnv -> Prop :=
      let addr_min := Params.enclave_base eid in
      let addr_max := Bits.plus (Params.enclave_base eid) (Params.enclave_size eid) in
      fun st input_log output_log =>
        let req_opt := match mem with
                       | CacheType_Imem => observe_imem_reqs_to_mem output_log core_id
                       | CacheType_Dmem => observe_dmem_reqs_to_mem output_log core_id
                       end in
        match req_opt with
        | None => True
        | Some req =>
            let addr := mem_req_get_addr req in
            (Bits.unsigned_le addr_min addr = true) /\ (Bits.unsigned_lt addr addr_max = true)
        end.

    (* The proof itself is simpler, something like "output_is_a_function_of_partitioned_registers" *)
    (* TODO: need to include mention of shared state *)
    Theorem partitioned_when_in_reset_state:
      forall (core_id: ind_core_id) (st: state) (eid: enclave_id),
      valid_reset_state st core_id eid ->
      forall (n: nat),
      prop_holds_for_n_sm_steps n st (P_no_enclave_req core_id) ->
      prop_holds_for_n_sm_steps n st (P_partition core_id).
    Admitted.

    Theorem reqs_to_enclave_memory_in_range:
      forall (core_id: ind_core_id) (st: state) (eid: enclave_id),
      valid_reset_state st core_id eid ->
      forall (n: nat),
      prop_holds_for_n_sm_steps n st (P_no_enclave_req core_id) ->
      prop_holds_for_n_sm_steps n st (P_mem_reqs_in_range CacheType_Imem core_id eid) /\
      prop_holds_for_n_sm_steps n st (P_mem_reqs_in_range CacheType_Dmem core_id eid).
    Admitted.

    (* TODO: For context switching, state that core output is a function also of the other core's enclave *)

  End CycleModel.

End SecurityMonitor.

Module Type Machine_sig.
  Parameter reg_t : Type.
  Parameter ext_fn_t : Type.
  Parameter R : reg_t -> type.
  Parameter Sigma : ext_fn_t -> ExternalSignature.
  Parameter r : forall reg, R reg.
  Parameter rule_name_t : Type.
  Parameter rules : rule_name_t -> rule R Sigma.
  Parameter FiniteType_reg_t : FiniteType reg_t.
  Parameter schedule : Syntax.scheduler pos_t rule_name_t.
  Parameter ext_fn_specs : ext_fn_t -> ext_fn_spec.

End Machine_sig.

Module Type Memory_sig (External: External_sig).
  Parameter internal_reg_t : Type.
  Parameter R_internal : internal_reg_t -> type.
  Parameter r_internal : (forall (idx: internal_reg_t), R_internal idx).

  Import Common.

  Declare Instance FiniteType_internal_reg_t : FiniteType internal_reg_t.

  Inductive reg_t :=
  | toIMem0 (state: MemReq.reg_t)
  | toIMem1 (state: MemReq.reg_t)
  | toDMem0 (state: MemReq.reg_t)
  | toDMem1 (state: MemReq.reg_t)
  | fromIMem0 (state: MemResp.reg_t)
  | fromIMem1 (state: MemResp.reg_t)
  | fromDMem0 (state: MemResp.reg_t)
  | fromDMem1 (state: MemResp.reg_t)
  | purge0
  | purge1
  | internal (r: internal_reg_t)
  .

  Definition R (idx: reg_t) :=
    match idx with
    | toIMem0 st => MemReq.R st
    | toIMem1 st => MemReq.R st
    | toDMem0 st => MemReq.R st
    | toDMem1 st => MemReq.R st
    | fromIMem0 st => MemResp.R st
    | fromIMem1 st => MemResp.R st
    | fromDMem0 st => MemResp.R st
    | fromDMem1 st => MemResp.R st
    | purge0 => enum_t purge_state
    | purge1 => enum_t purge_state
    | internal st => R_internal st
    end.

  Definition r (idx: reg_t) : R idx :=
    match idx with
    | toIMem0 st => MemReq.r st
    | toIMem1 st => MemReq.r st
    | toDMem0 st => MemReq.r st
    | toDMem1 st => MemReq.r st
    | fromIMem0 st => MemResp.r st
    | fromIMem1 st => MemResp.r st
    | fromDMem0 st => MemResp.r st
    | fromDMem1 st => MemResp.r st
    | purge0 => value_of_bits (Bits.zero)
    | purge1 => value_of_bits (Bits.zero)
    | internal st => r_internal st
    end.


  Declare Instance FiniteType_reg_t : FiniteType reg_t.

  Definition ext_fn_t := External.ext_fn_t.
  Definition Sigma := External.Sigma.
  Definition rule := rule R Sigma.
  (* Definition sigma := External.sigma. *)

  Parameter rule_name_t : Type.
  Parameter rules  : rule_name_t -> rule.

  Axiom schedule : Syntax.scheduler pos_t rule_name_t.

End Memory_sig.


Module Machine (External: External_sig) (EnclaveParams: EnclaveParameters)
               (Params0: CoreParameters) (Params1: CoreParameters)
               (Core0: Core_sig External EnclaveParams Params0)
               (Core1: Core_sig External EnclaveParams Params1)
               (Memory: Memory_sig External) <: Machine_sig.

  Module SM := SecurityMonitor External EnclaveParams.

  Include Common.

  Inductive reg_t' : Type :=
  | core_id0
  | core_id1
  (* State purging *)
  | purge_core0
  | purge_core1
  | purge_mem0
  | purge_mem1
  (* Program counter? Doesn't /need/ to be here, but let's us avoid reasoning about Core code *)
  | pc0
  | pc1
  (* Register files *)
      (*
  | core0_rf (state: Rf.reg_t)
  | core1_rf (state: Rf.reg_t) 
  *)
  (* Core0 <-> SM *)
  | Core0ToSM_IMem (state: MemReq.reg_t)
  | Core0ToSM_DMem (state: MemReq.reg_t)
  | Core0ToSM_Enc (state: EnclaveReq.reg_t)
  | SMToCore0_IMem (state: MemResp.reg_t)
  | SMToCore0_DMem (state: MemResp.reg_t)
  (* Core1 <-> SM *)
  | Core1ToSM_IMem (state: MemReq.reg_t)
  | Core1ToSM_DMem (state: MemReq.reg_t)
  | Core1ToSM_Enc (state: EnclaveReq.reg_t)
  | SMToCore1_IMem (state: MemResp.reg_t)
  | SMToCore1_DMem (state: MemResp.reg_t)
  (* SM <-> Mem *)
  | SMToMem0_IMem (state: MemReq.reg_t)
  | SMToMem0_DMem (state: MemReq.reg_t)
  | SMToMem1_IMem (state: MemReq.reg_t)
  | SMToMem1_DMem (state: MemReq.reg_t)
  | MemToSM0_IMem (state: MemResp.reg_t)
  | MemToSM0_DMem (state: MemResp.reg_t)
  | MemToSM1_IMem (state: MemResp.reg_t)
  | MemToSM1_DMem (state: MemResp.reg_t)
  (* Internal registers *)
  | Core0_internal (state: Core0.internal_reg_t)
  | Core1_internal (state: Core1.internal_reg_t)
  | SM_internal (state: SM.internal_reg_t)
  | Mem_internal (state: Memory.internal_reg_t)
  .

  Definition reg_t := reg_t'.

  Definition R (idx: reg_t) : type :=
    match idx with
    | core_id0 => bits_t 1
    | core_id1 => bits_t 1
    (* State purging*)
    | purge_core0 => enum_t purge_state
    | purge_core1 => enum_t purge_state
    | purge_mem0 => enum_t purge_state
    | purge_mem1 => enum_t purge_state
    | pc0 => bits_t 32
    | pc1 => bits_t 32
    (* Register files *)
    (*
    | core0_rf st => Rf.R st
    | core1_rf st => Rf.R st
    *)
    (* Core0 <-> SM *)
    | Core0ToSM_IMem st => MemReq.R st
    | Core0ToSM_DMem st => MemReq.R st
    | Core0ToSM_Enc st => EnclaveReq.R st
    | SMToCore0_IMem st => MemResp.R st
    | SMToCore0_DMem st => MemResp.R st
    (* Core1 <-> SM *)
    | Core1ToSM_IMem st => MemReq.R st
    | Core1ToSM_DMem st => MemReq.R st
    | Core1ToSM_Enc st => EnclaveReq.R st
    | SMToCore1_IMem st => MemResp.R st
    | SMToCore1_DMem st => MemResp.R st
    (* SM <-> Mem *)
    | SMToMem0_IMem st => MemReq.R st
    | SMToMem0_DMem st => MemReq.R st
    | SMToMem1_IMem st => MemReq.R st
    | SMToMem1_DMem st => MemReq.R st
    | MemToSM0_IMem st => MemResp.R st
    | MemToSM0_DMem st => MemResp.R st
    | MemToSM1_IMem st => MemResp.R st
    | MemToSM1_DMem st => MemResp.R st
    (* Internal registers *)
    | Core0_internal st => Core0.R_internal st
    | Core1_internal st => Core1.R_internal st
    | SM_internal st => SM.R_internal st
    | Mem_internal st => Memory.R_internal st
    end.

  Definition r (idx: reg_t) : R idx :=
    match idx with
    | core_id0 => Params0.core_id
    | core_id1 => Params1.core_id
    (* Purge state *)
    | purge_core0 => value_of_bits (Bits.zero)
    | purge_core1 => value_of_bits (Bits.zero)
    | purge_mem0 => value_of_bits (Bits.zero)
    | purge_mem1 => value_of_bits (Bits.zero)
    | pc0 => Params0.initial_pc
    | pc1 => Params1.initial_pc
    (* Register files *)
    (*
    | core0_rf st => Rf.r st
    | core1_rf st => Rf.r st
    *)
    (* Core0 <-> SM *)
    | Core0ToSM_IMem st => MemReq.r st
    | Core0ToSM_DMem st => MemReq.r st
    | Core0ToSM_Enc st => EnclaveReq.r st
    | SMToCore0_IMem st => MemResp.r st
    | SMToCore0_DMem st => MemResp.r st
    (* Core1 <-> SM *)
    | Core1ToSM_IMem st => MemReq.r st
    | Core1ToSM_DMem st => MemReq.r st
    | Core1ToSM_Enc st => EnclaveReq.r st
    | SMToCore1_IMem st => MemResp.r st
    | SMToCore1_DMem st => MemResp.r st
    (* SM <-> Mem *)
    | SMToMem0_IMem st => MemReq.r st
    | SMToMem0_DMem st => MemReq.r st
    | SMToMem1_IMem st => MemReq.r st
    | SMToMem1_DMem st => MemReq.r st
    | MemToSM0_IMem st => MemResp.r st
    | MemToSM0_DMem st => MemResp.r st
    | MemToSM1_IMem st => MemResp.r st
    | MemToSM1_DMem st => MemResp.r st
    (* Internal registers *)
    | Core0_internal st => Core0.r_internal st
    | Core1_internal st => Core1.r_internal st
    | SM_internal st => SM.r_internal st
    | Mem_internal st => Memory.r_internal st
    end.

  Definition ext_fn_t := External.ext_fn_t.
  Definition Sigma := External.Sigma.
  Definition ext_fn_specs := External.ext_fn_specs.
  Definition rule : Type := rule R Sigma.

  (* TODO: 40s *)
  Instance FiniteType_reg_t : FiniteType reg_t := _.
  (* Declare Instance FiniteType_reg_t : FiniteType reg_t.   *)

  Instance EqDec_reg_t : EqDec reg_t := _.

  Inductive rule_name_t' :=
  | Core0Rule (r: Core0.rule_name_t)
  | Core1Rule (r: Core1.rule_name_t)
  | SmRule   (r: SM.rule_name_t)
  | MemRule  (r: Memory.rule_name_t)
  .

  Definition rule_name_t := rule_name_t'.

  Section Core0_Lift.
    Definition core0_lift (reg: Core0.reg_t) : reg_t :=
      match reg with
      | Core0.core_id => core_id0
      | Core0.toIMem s => Core0ToSM_IMem s
      | Core0.toDMem s => Core0ToSM_DMem s
      | Core0.toSMEnc s => Core0ToSM_Enc s
      | Core0.fromIMem s => SMToCore0_IMem s
      | Core0.fromDMem s => SMToCore0_DMem s
      (* | Core0.rf s => core0_rf s *)
      | Core0.pc => pc0
      | Core0.purge => purge_core0
      | Core0.internal s => Core0_internal s
      end.

    Definition Lift_core0 : RLift _ Core0.reg_t reg_t Core0.R R := ltac:(mk_rlift core0_lift).
    Definition FnLift_core0 : RLift _ Core0.ext_fn_t ext_fn_t Core0.Sigma Sigma := ltac:(lift_auto).

  End Core0_Lift.

  Section Core1_Lift.
    Definition core1_lift (reg: Core1.reg_t) : reg_t :=
      match reg with
      | Core1.core_id => core_id1
      | Core1.toIMem s => Core1ToSM_IMem s
      | Core1.toDMem s => Core1ToSM_DMem s
      | Core1.toSMEnc s => Core1ToSM_Enc s
      | Core1.fromIMem s => SMToCore1_IMem s
      | Core1.fromDMem s => SMToCore1_DMem s
      (* | Core1.rf s => core1_rf s *)
      | Core1.pc => pc1
      | Core1.purge => purge_core1
      | Core1.internal s => Core1_internal s
      end.

    Definition Lift_core1 : RLift _ Core1.reg_t reg_t Core1.R R := ltac:(mk_rlift core1_lift).
    Definition FnLift_core1 : RLift _ Core1.ext_fn_t ext_fn_t Core1.Sigma Sigma := ltac:(lift_auto).

  End Core1_Lift.

  Section SM_Lift.

    Definition sm_lift (reg: SM.reg_t) : reg_t :=
      match reg with
      | SM.fromCore0_IMem st => Core0ToSM_IMem st
      | SM.fromCore0_DMem st => Core0ToSM_DMem st
      | SM.fromCore0_Enc st => Core0ToSM_Enc st
      | SM.toCore0_IMem st => SMToCore0_IMem st
      | SM.toCore0_DMem st => SMToCore0_DMem st
      (* Core1 <-> SM *)
      | SM.fromCore1_IMem st => Core1ToSM_IMem st
      | SM.fromCore1_DMem st => Core1ToSM_DMem st
      | SM.fromCore1_Enc st => Core1ToSM_Enc st
      | SM.toCore1_IMem st => SMToCore1_IMem st
      | SM.toCore1_DMem st => SMToCore1_DMem st
      (* SM <-> Mem *)
      | SM.toMem0_IMem st => SMToMem0_IMem st
      | SM.toMem0_DMem st => SMToMem0_DMem st
      | SM.toMem1_IMem st => SMToMem1_IMem st
      | SM.toMem1_DMem st => SMToMem1_DMem st
      | SM.fromMem0_IMem st => MemToSM0_IMem st
      | SM.fromMem0_DMem st => MemToSM0_DMem st
      | SM.fromMem1_IMem st => MemToSM1_IMem st
      | SM.fromMem1_DMem st => MemToSM1_DMem st
      (* pc *)
      | SM.pc_core0 => pc0
      | SM.pc_core1 => pc1
      (* purge *)
      | SM.purge_core0 => purge_core0
      | SM.purge_core1 => purge_core1
      | SM.purge_mem0 => purge_mem0
      | SM.purge_mem1 => purge_mem1
      | SM.internal st => SM_internal st
      end.

    Definition Lift_sm : RLift _ SM.reg_t reg_t SM.R R := ltac:(mk_rlift sm_lift).
    Definition FnLift_sm : RLift _ SM.ext_fn_t ext_fn_t SM.Sigma Sigma := ltac:(lift_auto).

  End SM_Lift.

  Section Mem_Lift.
    Definition mem_lift (reg: Memory.reg_t) : reg_t :=
      match reg with
      | Memory.toIMem0 st => SMToMem0_IMem st
      | Memory.toIMem1 st => SMToMem1_IMem st
      | Memory.toDMem0 st => SMToMem0_DMem st
      | Memory.toDMem1 st => SMToMem1_DMem st
      | Memory.fromIMem0 st => MemToSM0_IMem st
      | Memory.fromIMem1 st => MemToSM1_IMem st
      | Memory.fromDMem0 st => MemToSM0_DMem st
      | Memory.fromDMem1 st => MemToSM1_DMem st
      | Memory.purge0 => purge_mem0
      | Memory.purge1 => purge_mem1
      | Memory.internal st => Mem_internal st
      end.

    Definition Lift_mem : RLift _ Memory.reg_t reg_t Memory.R R := ltac:(mk_rlift mem_lift).
    Definition FnLift_mem : RLift _ Memory.ext_fn_t ext_fn_t Memory.Sigma Sigma := ltac:(lift_auto).

  End Mem_Lift.

  Section Rules.
    Definition core0_rule_name_lift (rl: Core0.rule_name_t) : rule_name_t :=
      Core0Rule rl.
    Definition core1_rule_name_lift (rl: Core1.rule_name_t) : rule_name_t :=
      Core1Rule rl.
    Definition sm_rule_name_lift (rl: SM.rule_name_t) : rule_name_t :=
      SmRule rl.
    Definition mem_rule_name_lift (rl: Memory.rule_name_t) : rule_name_t :=
      MemRule rl.

    Definition core0_rules (rl: Core0.rule_name_t) : rule :=
      lift_rule Lift_core0 FnLift_core0 (Core0.rules rl).
    Definition core1_rules (rl: Core1.rule_name_t) : rule :=
      lift_rule Lift_core1 FnLift_core1 (Core1.rules rl).
    Definition sm_rules (rl: SM.rule_name_t) : rule :=
      lift_rule Lift_sm FnLift_sm (SM.rules rl).
    Definition mem_rules (rl: Memory.rule_name_t) : rule :=
      lift_rule Lift_mem FnLift_mem (Memory.rules rl).

    Definition rules (rl: rule_name_t) : rule :=
      match rl with
      | Core0Rule r => core0_rules r
      | Core1Rule r => core1_rules r
      | SmRule r => sm_rules r
      | MemRule r => mem_rules r
      end.

  End Rules.

  Section Schedule.
    Definition core0_schedule := lift_scheduler core0_rule_name_lift Core0.schedule.
    Definition core1_schedule := lift_scheduler core1_rule_name_lift Core1.schedule.
    Definition sm_schedule := lift_scheduler sm_rule_name_lift SM.schedule.
    Definition mem_schedule := lift_scheduler mem_rule_name_lift Memory.schedule.

    Definition schedule :=
      core0_schedule ||> core1_schedule ||> sm_schedule ||> mem_schedule.

  End Schedule.

  Definition reg_state : Type := env_t ContextEnv (fun idx: reg_t => R idx).

End Machine.
