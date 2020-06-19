Require Import Koika.Frontend.
Require Import Coq.Lists.List.

Require Import Koika.Std.

Require Import dynamic_isolation.External.
Require Import dynamic_isolation.Framework.
Require Import dynamic_isolation.Interfaces.
Require Import dynamic_isolation.LogHelpers.
Require Import dynamic_isolation.Multicore.
Require Import dynamic_isolation.Tactics.

(*
Module Pf (External: External_sig) (EnclaveParams: EnclaveParameters)
          (Params0: CoreParameters) (Params1: CoreParameters)
          (Core0: Core_sig External EnclaveParams Params0)
          (Core1: Core_sig External EnclaveParams Params1)
          (Memory: Memory_sig External).
  Module Impl:= MachineSemantics External EnclaveParams Params0 Params1 Core0 Core1 Memory.
  Import Common.
  Import Interfaces.Common.

  Record enclave_metadata :=
    { meta_eid : enclave_id;
      shared_page : bool
    }.

  Record enclave_params :=
    { metadata : enclave_metadata;
      param_dram: dram_t
    }.

  Record core_config : Type :=
    { enclave_data : enclave_metadata;
      in_limbo: bool;
      requested_enclave: option enclave_metadata;
      state_fn : nat -> observations_t
    }.

  Definition rf_t : Type := env_t ContextEnv Rf.R.

  Definition isolated_function_t : Type := ind_core_id -> enclave_params -> rf_t -> nat -> observations_t.

  Record partitioned_memory :=
    { pm_enclave_mem : enclave_id -> option dram_t;
      pm_shared_page : option dram_t;
    }.

  Record ghost_state :=
    { core0_config : core_config;
      core1_config : core_config;
      mem_partitions : partitioned_memory;
      num_cycles : nat
    }.


  (* TODO: This should be derived from Interfaces *)
  Definition initial_rf : rf_t := ContextEnv.(create) Rf.r.

  Definition mk_initial_config (fn: isolated_function_t) (core_id: ind_core_id)
                               (params: enclave_params) (rf: rf_t) : core_config :=
    {| enclave_data := params.(metadata);
       in_limbo := false;
       requested_enclave := None;
       state_fn := fn core_id params rf
    |}.

  Definition enclave_base enc_id := Bits.to_nat (EnclaveParams.enclave_base enc_id).
  Definition enclave_max enc_id := Bits.to_nat (Bits.plus (EnclaveParams.enclave_base enc_id)
                                                          (EnclaveParams.enclave_size enc_id)).

  Definition initial_enclave_dram initial_dram enc_id : dram_t :=
    fun addr => if ((enclave_base enc_id) <=? addr) && (addr <? (enclave_max enc_id))
             then initial_dram addr
             else None.

  Definition initial_shared_mem initial_dram : dram_t :=
    fun addr => if ((Bits.to_nat (EnclaveParams.shared_mem_base) <=? addr) &&
                 (addr <? Bits.to_nat (Bits.plus EnclaveParams.shared_mem_base EnclaveParams.shared_mem_size)))
             then initial_dram addr
             else None.

  Definition mk_initial_pm (initial_dram: dram_t) : partitioned_memory :=
    {| pm_enclave_mem := fun eid => Some (initial_enclave_dram initial_dram eid);
       pm_shared_page := Some (initial_shared_mem initial_dram)
    |}.

  Definition initial_ghost_state (fn: isolated_function_t) (initial_dram: dram_t) : ghost_state :=
    let enclave0_param :=
        {| metadata := {| meta_eid := Enclave0;
                          shared_page := false
                       |};
           param_dram := initial_enclave_dram initial_dram Enclave0
        |} in
    let enclave1_param :=
        {| metadata := {| meta_eid := Enclave1;
                          shared_page := false
                       |};
           param_dram := initial_enclave_dram initial_dram Enclave1
        |} in
    {| core0_config := mk_initial_config fn CoreId0 enclave0_param initial_rf;
       core1_config := mk_initial_config fn CoreId1 enclave1_param initial_rf;
       mem_partitions := {| pm_enclave_mem := fun eid => match eid with
                                                      | (Enclave0 | Enclave1) => None
                                                      | _ => Some (initial_enclave_dram initial_dram eid)
                                                      end;
                            pm_shared_page := Some (initial_shared_mem initial_dram)
                         |};
       num_cycles := 0
    |}.

  (* TODO: Do we care about cycle-accurate purge? *)
  Inductive function_generates_trace_helper
            (fn: isolated_function_t) (initial_dram: dram_t)
            (ghost: ghost_state) (tr: trace) : Prop :=
  | EmptyTrace :
      forall (initial_ghost : ghost = initial_ghost_state fn initial_dram)
        (empty_trace: tr = []),
      function_generates_trace_helper fn initial_dram ghost tr
  | IndTrace_BothRunning :
      forall (prev_tr: trace) (obs: ind_core_id -> observations_t)
        (prev_ghost: ghost_state) (ghost0 ghost1: ghost_state)

        (* Induction hypothesis *)
        (ind_hyp: function_generates_trace_helper fn initial_dram prev_ghost prev_tr)
        (* If Core0 is running an enclave,
         * fn must generate the relevant observation
         *)
        (pf_case_core0_running : prev_ghost.(core0_config).(in_limbo) = false ->
                                 obs CoreId0 = prev_ghost.(core0_config).(state_fn) (S prev_ghost.(num_cycles))
        )
        (* If Core0 is not running an enclave *)
        (pf_case_core0_limbo : prev_ghost.(core0_config).(in_limbo) = true ->
                               obs CoreId0 = prev_ghost.(core0_config).(state_fn) (S prev_ghost.(num_cycles))
        )


        (* If Core1 is running an enclave *)
        (* If Core1 is not running an enclave *)


        (core0_running : prev_ghost.(core0_config).(in_limbo) = false)
        (core1_running : prev_ghost.(core1_config).(in_limbo) = false)
        (trace_eq: tr = prev_tr ++ [obs]),
        (*
        (ghost0_eq: ghost0 =
        (ghost1_eq: ghost1 =

        (cur_obs.obs_enclave_req
        *)
        (* TODO *)
      function_generates_trace_helper fn initial_dram ghost tr.



  Definition function_generates_trace (fn: isolated_function_t) (initial_dram: dram_t) (tr: trace) : Prop :=
    exists ghost_state, function_generates_trace_helper fn initial_dram ghost_state tr.


  Section Initialised.
    Variable initial_dram: dram_t.

    Theorem simulation: exists (iso_fn : isolated_function_t),
      forall (n: nat) (impl_st: Impl.state) (impl_tr: trace),
        Impl.step_n initial_dram n = (impl_st, impl_tr) ->
        function_generates_trace iso_fn initial_dram impl_tr.
    Admitted.

  End Initialised.

End Pf.
*)

Module SMProperties (External: External_sig) (Params: EnclaveParameters).
  Module SM := SecurityMonitor External Params.
  Include SM.
  Import Interfaces.Common.
  Import Interfaces.EnclaveInterface.

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

    (* More generic framework:
     * time partition based on contents of a register, which is deterministic.
     * So function from time to taint.
     * Idea is that equivalence holds as an independent function of time?;
     * Note: SM is entirely spatially partitioned. Normally this would need to be a function of time too
     *)
    Definition internal_reg_to_taint (reg: internal_reg_t) : option ind_core_id :=
      match reg with
      | state0 => Some CoreId0
      | state1 => Some CoreId1
      | enc_data0 => Some CoreId0
      | enc_data1 => Some CoreId1
      | enc_req0 => Some CoreId0
      | enc_req1 => Some CoreId1
      | clk => None
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
               (eid0: option enclave_id) (eid1: option enclave_id) (clk: bits_t 1)
               (idx: internal_reg_t) : R_internal idx :=
      match idx with
      | state0 => value_of_bits Bits.zero
      | state1 => value_of_bits Bits.zero
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
      | enc_req0 => value_of_bits (Bits.zero)
      | enc_req1 => value_of_bits (Bits.zero)
      | clk => clk
      end.

    Definition initialise_with_eid (eid0: option enclave_id) (eid1: option enclave_id) (clk: bits_t 1) (idx: reg_t) : R idx :=
      match idx with
      | internal s => initialise_internal_with_eid eid0 eid1 clk s
      | s => r s
      end.

  End Initialise.

  Section ValidResetState.

    (* TODO: not quite complete. *)
    Definition valid_reset_state (st: state) (core_id: ind_core_id) (eid: enclave_id): Prop :=
      forall reg, reg_to_taint reg = Some core_id ->
             (reg <> pc_core0 /\ reg <> pc_core1) ->
             match core_id with
             | CoreId0 => initialise_with_eid (Some eid) None Ob~0 reg = ContextEnv.(getenv) st reg
             | CoreId1 => initialise_with_eid None (Some eid) Ob~0 reg = ContextEnv.(getenv) st reg
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

    Definition state_eq (st: state) (core_id: ind_core_id) (v: enum_t core_state): Prop :=
      match core_id with
      | CoreId0 => ContextEnv.(getenv) st (internal state0) = v
      | CoreId1 => ContextEnv.(getenv) st (internal state1) = v
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
      state_eq st0 core_id (value_of_bits Bits.zero) ->
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
      not (state_eq st core_id (value_of_bits Bits.zero)) ->
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
    Variable pf_feedback_fn_generates_valid_log
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
End SMProperties.

(* TODO: move this *)

Module TradPf (External: External_sig) (EnclaveParams: EnclaveParameters)
          (Params0: CoreParameters) (Params1: CoreParameters)
          (Core0: Core_sig External EnclaveParams Params0)
          (Core1: Core_sig External EnclaveParams Params1)
          (Memory: Memory_sig External).
  Module Impl:= MachineSemantics External EnclaveParams Params0 Params1 Core0 Core1 Memory.
  Module Spec:= IsolationSemantics External EnclaveParams Params0 Params1 Core0 Core1 Memory.

  Import Common.

  (* ================= TMP ====================== *)
  Definition impl_log_t : Type := Impl.log_t.

  (* ================= END_TMP ====================== *)

  Section GhostState.

    Definition impl_ghost_state : Type. Admitted.
    Definition spec_ghost_state : Type. Admitted.

    Definition initial_impl_ghost : impl_ghost_state. Admitted.
    Definition initial_spec_ghost : spec_ghost_state. Admitted.

    Definition impl_step_with_ghost (st: Impl.state * impl_ghost_state)
                                    : (Impl.state * impl_ghost_state) * tau :=
      let (impl_st, ghost_st) := st in
      ((fst (Impl.step impl_st), ghost_st (* TODO *)), (snd (Impl.step impl_st))).

    Definition spec_step_with_ghost (st: Spec.state * spec_ghost_state)
                                    : (Spec.state * spec_ghost_state) * tau :=
      let (spec_st, ghost_st) := st in
      ((fst (Spec.step spec_st), ghost_st (* TODO *)), (snd (Spec.step spec_st))).

    Section Initialised.
      Context (initial_dram : dram_t).

      Definition impl_step_n_with_ghost (n: nat) : (Impl.state * impl_ghost_state) * trace :=
        step_n (Impl.initial_state initial_dram, initial_impl_ghost)
               impl_step_with_ghost
               n.

      Definition spec_step_n_with_ghost (n: nat) : (Spec.state * spec_ghost_state) * trace :=
        step_n (Spec.initial_state initial_dram, initial_spec_ghost)
               spec_step_with_ghost
               n.

    End Initialised.
Import Tactics.
    Section Lemmas.

      Lemma impl_drop_ghost :
        forall (initial_dram: dram_t)
          n st st' evs evs',
          impl_step_n_with_ghost initial_dram n = (st, evs) ->
          Impl.step_n initial_dram n = (st', evs') ->
          st' = fst st /\ evs = evs'.
      Proof.
        intro. eapply proj_step_fn_eq.
        - unfold is_proj; auto.
        - unfold natural_step_fn. unfold impl_step_with_ghost, is_proj.
          intros; destruct_all_matches.
      Qed.

      Lemma spec_drop_ghost :
        forall (initial_dram: dram_t)
          n st st' evs evs',
          spec_step_n_with_ghost initial_dram n = (st, evs) ->
          Spec.step_n initial_dram n = (st', evs') ->
          st' = fst st /\ evs = evs'.
      Proof.
        intro. eapply proj_step_fn_eq.
        - unfold is_proj; auto.
        - unfold natural_step_fn. unfold spec_step_with_ghost, is_proj.
          intros; destruct_all_matches.
      Qed.


    End Lemmas.

  End GhostState.

  Ltac destruct_pair :=
    match goal with
    | [ P : _ * _ |- _ ] =>
      let p1 := fresh P in
      let p2 := fresh P in
      destruct P as [p1 p2]
  end.

  Definition impl_state_t : Type := Impl.state * impl_ghost_state.
  Definition spec_state_t : Type := Spec.state * spec_ghost_state.

  Definition Sim : impl_state_t -> spec_state_t -> Prop.
  Admitted.

  Section Initialised.
    Variable initial_dram: dram_t.

    Theorem initial_state_sim :
      Sim (Impl.initial_state initial_dram, initial_impl_ghost)
          (Spec.initial_state initial_dram, initial_spec_ghost).
    Admitted.

    Theorem step_sim : forall (impl_st impl_st': impl_state_t) (spec_st spec_st': spec_state_t)
                         (impl_tau spec_tau: tau),
      Sim impl_st spec_st ->
      impl_step_with_ghost impl_st = (impl_st', impl_tau) ->
      spec_step_with_ghost spec_st = (spec_st', spec_tau) ->
      Sim impl_st' spec_st' /\ impl_tau = spec_tau.
    Admitted.

    Theorem step_n_sim : forall (n: nat)
                         (impl_st: Impl.state) (impl_tr: trace) (impl_ghost: impl_ghost_state)
                         (spec_st: Spec.state) (spec_tr: trace) (spec_ghost: spec_ghost_state),
        impl_step_n_with_ghost initial_dram n = ((impl_st, impl_ghost), impl_tr) ->
        spec_step_n_with_ghost initial_dram n = ((spec_st, spec_ghost), spec_tr) ->
        Sim (impl_st, impl_ghost) (spec_st, spec_ghost) /\ impl_tr = spec_tr.
    Proof.
      induction n.
      - intros; simplify_all; split_cases; auto.
        apply initial_state_sim.
      - simpl; intros; destruct_all_matches; simplify_all.
        repeat destruct_pair.
        specialize IHn with (1 := eq_refl) (2 := eq_refl); propositional.
        match goal with
        | [ H0: Sim _ _,
            H1: impl_step_with_ghost _ = _,
            H2: spec_step_with_ghost _ = _ |- _ ] =>
          specialize step_sim with (1 := H0) (2 := H1) (3 := H2)
        end.
        intuition.
    Qed.

    Theorem refinement: forall (n: nat)
                          (impl_st: Impl.state) (impl_tr: trace)
                          (spec_st: Spec.state) (spec_tr: trace),
        Impl.step_n initial_dram n = (impl_st, impl_tr) ->
        Spec.step_n initial_dram n = (spec_st, spec_tr) ->
        impl_tr = spec_tr.
    Proof.
      intros *; intros H_impl H_spec.
      destruct (impl_step_n_with_ghost initial_dram n) as [[impl_st' impl_ghost] impl_tr'] eqn:Heq_impl.
      destruct (spec_step_n_with_ghost initial_dram n) as [[spec_st' spec_ghost] spec_tr'] eqn:Heq_spec.
      edestruct impl_drop_ghost with (1 := Heq_impl) (2 := H_impl).
      edestruct spec_drop_ghost with (1 := Heq_spec) (2 := H_spec).
      simplify_all.
      eapply step_n_sim; eauto.
    Qed.

  End Initialised.

End TradPf.
