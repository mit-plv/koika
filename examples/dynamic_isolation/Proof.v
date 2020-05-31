Require Import Koika.Frontend.
Require Import Coq.Lists.List.

Require Import Koika.Std.

Require Import DynamicIsolation.Interfaces.
Require Import DynamicIsolation.External.
Require Import DynamicIsolation.Multicore.

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
      param_dram: initial_dram_t
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
    { pm_enclave_mem : enclave_id -> option initial_dram_t;
      pm_shared_page : option initial_dram_t;
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

  Definition initial_enclave_dram initial_dram enc_id : initial_dram_t :=
    fun addr => if ((enclave_base enc_id) <=? addr) && (addr <? (enclave_max enc_id))
             then initial_dram addr
             else None.

  Definition initial_shared_mem initial_dram : initial_dram_t :=
    fun addr => if ((Bits.to_nat (EnclaveParams.shared_mem_base) <=? addr) &&
                 (addr <? Bits.to_nat (Bits.plus EnclaveParams.shared_mem_base EnclaveParams.shared_mem_size)))
             then initial_dram addr
             else None.

  Definition mk_initial_pm (initial_dram: initial_dram_t) : partitioned_memory :=
    {| pm_enclave_mem := fun eid => Some (initial_enclave_dram initial_dram eid);
       pm_shared_page := Some (initial_shared_mem initial_dram)
    |}.

  Definition initial_ghost_state (fn: isolated_function_t) (initial_dram: initial_dram_t) : ghost_state :=
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
            (fn: isolated_function_t) (initial_dram: initial_dram_t)
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



  Definition function_generates_trace (fn: isolated_function_t) (initial_dram: initial_dram_t) (tr: trace) : Prop :=
    exists ghost_state, function_generates_trace_helper fn initial_dram ghost_state tr.


  Section Initialised.
    Variable initial_dram: initial_dram_t.

    Theorem simulation: exists (iso_fn : isolated_function_t),
      forall (n: nat) (impl_st: Impl.state) (impl_tr: trace),
        Impl.step_n initial_dram n = (impl_st, impl_tr) ->
        function_generates_trace iso_fn initial_dram impl_tr.
    Admitted.

  End Initialised.

End Pf.



Module OldPf (External: External_sig) (EnclaveParams: EnclaveParameters)
          (Params0: CoreParameters) (Params1: CoreParameters)
          (Core0: Core_sig External EnclaveParams Params0)
          (Core1: Core_sig External EnclaveParams Params1)
          (Memory: Memory_sig External).
  Module Impl:= MachineSemantics External EnclaveParams Params0 Params1 Core0 Core1 Memory.
  Module Spec:= IsolationSemantics External EnclaveParams Params0 Params1 Core0 Core1 Memory.

  Import Common.

  Section Initialised.
    Variable initial_dram: initial_dram_t.

    Theorem simulation: forall (n: nat)
                          (impl_st: Impl.state) (impl_tr: trace)
                          (spec_st: Spec.state) (spec_tr: trace),
        Impl.step_n initial_dram n = (impl_st, impl_tr) ->
        Spec.step_n  initial_dram n = (spec_st, spec_tr) ->
        impl_tr = spec_tr.
     Admitted.

  End Initialised.

End OldPf.
