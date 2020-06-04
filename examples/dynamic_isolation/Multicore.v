Require Import Koika.Frontend.
Require Import Coq.Lists.List.

Require Import Koika.Std.

Require Import dynamic_isolation.Interfaces.
Require Import dynamic_isolation.External.

Module Common.
  Import Interfaces.Common.

  Record req_observations_t :=
    ReqObs { obs_imem_req : option (struct_t mem_req);
             obs_dmem_req : option (struct_t mem_req);
             obs_enclave_req : option (struct_t enclave_req)
           }.

  (* TODO: We want to talk about the moment when context switching ends *)
  Record resp_observations_t :=
    RespObs { obs_imem_resp : option (struct_t mem_resp);
              obs_dmem_resp : option (struct_t mem_resp);
              obs_enclave_resp : bool
            }.

  Record observations_t :=
    Obs { obs_reqs : req_observations_t;
          obs_resps : resp_observations_t
        }.

  Definition tau := ind_core_id -> observations_t.
  Definition local_trace := list observations_t.
  Definition trace := list tau.

  Definition initial_dram_t : Type := nat -> option data_t.

End Common.

Module MachineSemantics (External: External_sig) (EnclaveParams: EnclaveParameters)
                        (Params0: CoreParameters) (Params1: CoreParameters)
                        (Core0: Core_sig External EnclaveParams Params0)
                        (Core1: Core_sig External EnclaveParams Params1)
                        (Memory: Memory_sig External).
  Module System := Machine External EnclaveParams
                           Params0 Params1
                           Core0 Core1
                           Memory.
  Import System.
  Import Common.

  Definition koika_state : Type := env_t ContextEnv (fun idx : reg_t => R idx).
  Definition placeholder_external_state : Type. Admitted.

  Definition TODO_external_sigma : (forall fn: ext_fn_t, Sig_denote (Sigma fn)). Admitted.
  Definition state : Type := koika_state * placeholder_external_state.

  Definition get_dram : state -> initial_dram_t. Admitted.
  Definition get_rf : state -> env_t ContextEnv Rf.R. Admitted.
  Definition update_function (st: state) (log: Log R ContextEnv) : Log R ContextEnv * placeholder_external_state.
  Admitted.

  (* Everything reset except for rf and eid *)
  Definition spin_up_machine (rf: env_t ContextEnv Rf.R) (eid: enclave_id) (initial_dram: initial_dram_t)
                             : state.
  Admitted.

  (* Replace enclave data *)
  Definition update_state_with_enclave_data (st: state) (core_id: ind_core_id) (eid: enclave_id): state. Admitted.

  Definition empty_log : Log R ContextEnv := log_empty.

  Require Import Tactics.

  Section Observations.

    (* TODO: generates code but requires dependent type rewrites *)
    Definition observe_imem_reqs' (core_id: ind_core_id) (log: Log R ContextEnv) : option (struct_t mem_req).
    Proof.
      remember (match core_id with | CoreId0 => (System.Core0ToSM_IMem MemReq.valid0,
                                                System.Core0ToSM_IMem MemReq.data0)
                                   | CoreId1 => (System.Core1ToSM_IMem MemReq.valid0,
                                                System.Core1ToSM_IMem MemReq.data0)
                end
               ) as regs; destruct regs as (reg_valid, reg_data).
      set (latest_write0 log reg_data) as ret_value.
      destruct_with_eqn (latest_write0 log reg_valid).
      - destruct core_id; (inversion Heqregs; subst; case_eq (Bits.single t); intros; [ exact ret_value | exact None]).
      - exact None.
    Defined.

    Definition observe_imem_reqs0 (log: Log R ContextEnv) : option (struct_t mem_req) :=
      match latest_write0 log (System.Core0ToSM_IMem MemReq.valid0) with
      | Some b =>
          if Bits.single b then (latest_write0 log (System.Core0ToSM_IMem MemReq.data0)) else None
      | None => None
      end.

    Definition observe_imem_reqs1 (log: Log R ContextEnv) : option (struct_t mem_req) :=
      match latest_write0 log (System.Core1ToSM_IMem MemReq.valid0) with
      | Some b =>
          if Bits.single b then (latest_write0 log (System.Core1ToSM_IMem MemReq.data0)) else None
      | None => None
      end.

    Definition observe_imem_reqs (log: Log R ContextEnv) (core_id: ind_core_id) : option (struct_t mem_req) :=
      match core_id with
      | CoreId0 => observe_imem_reqs0 log
      | CoreId1 => observe_imem_reqs1 log
      end.

    Definition observe_dmem_reqs0 (log: Log R ContextEnv) : option (struct_t mem_req) :=
      match latest_write0 log (System.Core0ToSM_DMem MemReq.valid0) with
      | Some b =>
          if Bits.single b then (latest_write0 log (System.Core0ToSM_DMem MemReq.data0)) else None
      | None => None
      end.

    Definition observe_dmem_reqs1 (log: Log R ContextEnv) : option (struct_t mem_req) :=
      match latest_write0 log (System.Core1ToSM_DMem MemReq.valid0) with
      | Some b =>
          if Bits.single b then (latest_write1 log (System.Core1ToSM_DMem MemReq.data0)) else None
      | None => None
      end.

    Definition observe_dmem_reqs (log: Log R ContextEnv) (core_id: ind_core_id) : option (struct_t mem_req) :=
      match core_id with
      | CoreId0 => observe_dmem_reqs0 log
      | CoreId1 => observe_dmem_reqs1 log
      end.

    Definition observe_enclave_reqs0 (log: Log R ContextEnv) : option (struct_t enclave_req) :=
      match latest_write0 log (System.Core0ToSM_Enc EnclaveReq.valid0) with
      | Some b =>
          if Bits.single b then (latest_write0 log (System.Core0ToSM_Enc EnclaveReq.data0)) else None
      | None => None
      end.

    Definition observe_enclave_reqs1 (log: Log R ContextEnv) : option (struct_t enclave_req) :=
      match latest_write0 log (System.Core1ToSM_Enc EnclaveReq.valid0) with
      | Some b =>
          if Bits.single b then (latest_write0 log (System.Core1ToSM_Enc EnclaveReq.data0)) else None
      | None => None
      end.

    Definition observe_enclave_reqs (log: Log R ContextEnv) (core_id: ind_core_id) : option (struct_t enclave_req) :=
      match core_id with
      | CoreId0 => observe_enclave_reqs0 log
      | CoreId1 => observe_enclave_reqs1 log
      end.

    Definition observe_reqs (log: Log R ContextEnv) (core_id: ind_core_id) : req_observations_t :=
      {| obs_imem_req := observe_imem_reqs log core_id;
         obs_dmem_req := observe_dmem_reqs log core_id;
         obs_enclave_req := observe_enclave_reqs log core_id
      |}.

    Definition observe_imem_resps0 (log: Log R ContextEnv) : option (struct_t mem_resp) :=
      match latest_write1 log (System.SMToCore0_IMem MemResp.valid0) with
      | Some b =>
          if Bits.single b then (latest_write1 log (System.SMToCore0_IMem MemResp.data0)) else None
      | None => None
      end.

    Definition observe_imem_resps1 (log: Log R ContextEnv) : option (struct_t mem_resp) :=
      match latest_write1 log (System.SMToCore1_IMem MemResp.valid0) with
      | Some b =>
          if Bits.single b then (latest_write1 log (System.SMToCore1_IMem MemResp.data0)) else None
      | None => None
      end.

    Definition observe_imem_resps (log: Log R ContextEnv) (core_id: ind_core_id) : option (struct_t mem_resp) :=
      match core_id with
      | CoreId0 => observe_imem_resps0 log
      | CoreId1 => observe_imem_resps1 log
      end.

    Definition observe_dmem_resps0 (log: Log R ContextEnv) : option (struct_t mem_resp) :=
      match latest_write1 log (System.SMToCore0_DMem MemResp.valid0) with
      | Some b =>
          if Bits.single b then (latest_write1 log (System.SMToCore0_DMem MemResp.data0)) else None
      | None => None
      end.

    Definition observe_dmem_resps1 (log: Log R ContextEnv) : option (struct_t mem_resp) :=
      match latest_write1 log (System.SMToCore1_DMem MemResp.valid0) with
      | Some b =>
          if Bits.single b then (latest_write1 log (System.SMToCore1_DMem MemResp.data0)) else None
      | None => None
      end.

    Definition observe_dmem_resps (log: Log R ContextEnv) (core_id: ind_core_id) : option (struct_t mem_resp) :=
      match core_id with
      | CoreId0 => observe_dmem_resps0 log
      | CoreId1 => observe_dmem_resps1 log
      end.

    (* TODO (slight hack): If write reg_proc_reset == Restart, treat as switching enclaves *)
    Definition observe_enclave_resp0 (log: Log R ContextEnv) : bool :=
      match latest_write log System.purge_core0 with
      | Some v => (Nat.eqb (Bits.to_nat v) 3)
      | None => false
      end.

    Definition observe_enclave_resp1 (log: Log R ContextEnv) : bool :=
      match latest_write log System.purge_core1 with
      | Some v => (Nat.eqb (Bits.to_nat v) 3)
      | None => false
      end.

    Definition observe_enclave_resps (log: Log R ContextEnv) (core_id: ind_core_id) : bool :=
      match core_id with
      | CoreId0 => observe_enclave_resp0 log
      | CoreId1 => observe_enclave_resp1 log
      end.

    Definition observe_resps (log: Log R ContextEnv) (core_id: ind_core_id) : resp_observations_t :=
      {| obs_imem_resp := observe_imem_resps log core_id;
         obs_dmem_resp := observe_dmem_resps log core_id;
         obs_enclave_resp := observe_enclave_resps log core_id
      |}.

    Definition do_observations (log: Log R ContextEnv) : ind_core_id -> observations_t :=
      fun core_id => {| obs_reqs := observe_reqs log core_id;
                     obs_resps := observe_resps log core_id
                  |}.

  End Observations.

  Definition step (st: state) : state * tau :=
    let (koika_st, ext_st) := st in
    let (log, ext_st') := update_function st log_empty in
    let obs := do_observations log in
    ((commit_update koika_st log, ext_st'), obs).

  Section Initialised.
    Variable initial_dram : initial_dram_t.

    Definition initial_external_state : placeholder_external_state. Admitted.

    Definition initial_state : state := (ContextEnv.(create) r, initial_external_state).

    Fixpoint step_n (n: nat) : state * trace :=
      match n with
      | 0 => (initial_state, [])
      | S n' =>
          let (st, evs) := step_n n' in
          let (st', ev) := step st in
          (st', evs ++ [ev])
      end.

  End Initialised.

End MachineSemantics.

Module IsolationSemantics (External: External_sig) (EnclaveParams: EnclaveParameters)
                          (Params0: CoreParameters) (Params1: CoreParameters)
                          (Core0: Core_sig External EnclaveParams Params0)
                          (Core1: Core_sig External EnclaveParams Params1)
                          (Memory: Memory_sig External).

  (* A system consists of two single-core machines with separate memories. *)
  Import Interfaces.Common.

  Record enclave_metadata :=
    { meta_eid : enclave_id;
      (*
      addr_min : bits_t 32;
      size : bits_t 32
      *)
    }.

  Record core_config : Type :=
    { enclave_data : enclave_metadata;
      in_limbo: bool;
      requested_enclave: option enclave_metadata
    }.

  Definition shared_enclave_config : Type := ind_core_id -> core_config.

  Module VoidCoreParams : CoreParameters.
    Definition core_id : Common.core_id_t := Bits.zero.
    Definition initial_pc : Common.addr_t := Bits.zero.
  End VoidCoreParams.

  Require Import dynamic_isolation.TrivialCore.

  Module VoidCore := EmptyCore External EnclaveParams VoidCoreParams.

  Module Machine0 := MachineSemantics External EnclaveParams Params0 VoidCoreParams Core0 VoidCore Memory.
  Module Machine1 := MachineSemantics External EnclaveParams VoidCoreParams Params1 VoidCore Core1 Memory.

  (* TODO: rename *)
  Definition initial_dram_t : Type := nat -> option data_t.


  Record state :=
    { machine0_state : Machine0.state;
      machine1_state : Machine1.state;
      enclave_config: shared_enclave_config;
      enclave_mem : enclave_id -> initial_dram_t;
      (* shared_mem : (initial_dram_t)  *)
    }.

  Import Common.

  (* Basic idea:
   * - We're allowed to update the private enclave state whenever the other enclave context switches
   * - This is signaled by "enclave_resp = true"
   * - We can model whether an enclave request is accepted (it waits until it can switch to the enclave for now)
   * - Give Core0 priority
   * - TODO: to prevent racing, we only allow one enclave resp at a time in the main system
   *)
  (* TODO: extract values better *)
  Definition enclave_req_to_eid (enclave_req: struct_t enclave_req) : option enclave_id :=
    let '(eid, _) := enclave_req in
    match Bits.to_nat eid with
    | 0 => Some Enclave0
    | 1 => Some Enclave1
    | 2 => Some Enclave2
    | 3 => Some Enclave3
    | _ => None
    end.

  Definition update_core_state (config: core_config) (obs: observations_t) : core_config :=
    match obs.(obs_reqs).(obs_enclave_req), obs.(obs_resps).(obs_enclave_resp) with
    | Some _, true => (* Should never happen *) config
    | Some req, false => if config.(in_limbo) then (* drop request *)
                          config
                        else match enclave_req_to_eid req with
                             | Some eid =>
                               {| enclave_data := config.(enclave_data);
                                  in_limbo := true;
                                  requested_enclave := Some {| meta_eid := eid |}
                               |}
                             | None => config (* drop request *)
                             end
    | None, true => match config.(requested_enclave) with
                   | None => (* Should never happen *) config
                   | Some eid => {| enclave_data := eid;
                                   in_limbo := false;
                                   requested_enclave := None
                                |}
                   end
    | None, false => config
    end.

  Record context_switch_data  :=
    { old_enclave: enclave_id;
      old_dram: initial_dram_t;
      new_enclave: enclave_id
    }.

  Definition do_context_switch (obs: observations_t) (old_config: core_config) (dram: initial_dram_t)
                               : option context_switch_data :=
    if obs.(obs_resps).(obs_enclave_resp) then
      match old_config.(requested_enclave) with
      | None => (* should not happen *) None
      | Some eid =>
        Some {| old_enclave := old_config.(enclave_data).(meta_eid);
                old_dram := dram;
                new_enclave := eid.(meta_eid)
             |}
      end
    else (* do nothing *)
      None.

  (* Top level theorem statement:
   * - more general but less immediately convincing: exists some function that no matter what input, gives some output
   * - except we really want to talk about context switching events, and say that when we're in an enclave, we're realy isolated
   * - is it possible to state this more generally? Do we gain anything?
   * - One idea is to write this in terms of
       "each time I enter an enclave, I can give you a function that completely defines the output up until
        I ask to context switch. And this function is a function of nothing except for the initial_dram and enclave         id (and, register file)
       "
   *)

  (* Communication model: when in limbo state, we can communicate enclave information.
   * Define what it means to enter limbo state
   *)
  Definition spin_up_machine0 (rf: env_t ContextEnv Rf.R) (eid: enclave_id) (initial_dram: initial_dram_t)
                              : Machine0.state :=
    Machine0.spin_up_machine rf eid initial_dram.

  Definition spin_up_machine1 (rf: env_t ContextEnv Rf.R) (eid: enclave_id) (initial_dram: initial_dram_t)
                              : Machine1.state :=
    Machine1.spin_up_machine rf eid initial_dram.

  Definition update_machine0_state (st: Machine0.state) (config: shared_enclave_config) : Machine0.state :=
    let config0 := config CoreId0 in
    let config1 := config CoreId1 in
    if config0.(in_limbo) then
      Machine0.update_state_with_enclave_data st CoreId1 config1.(enclave_data).(meta_eid)
    else st.

  Definition update_machine1_state (st: Machine1.state) (config: shared_enclave_config) : Machine1.state :=
    let config1 := config CoreId1 in
    let config0 := config CoreId0 in
    if config1.(in_limbo) then
      Machine1.update_state_with_enclave_data st CoreId0 config0.(enclave_data).(meta_eid)
    else st.


  (* TODO Cheat: time-partition entering an enclave:
   * Depending on cycle, can only enter on either even or odd cycle.
   *)

  Definition update_enclave_mem (enclave_mem: enclave_id -> initial_dram_t)
                                (eid: enclave_id) (dram: initial_dram_t) : enclave_id -> initial_dram_t :=
    fun eid' => match eid, eid' with
             | Enclave0, Enclave0 => dram
             | Enclave1, Enclave1 => dram
             | Enclave2, Enclave2 => dram
             | Enclave3, Enclave3 => dram
             | _, _ => enclave_mem eid'
             end.

  (* TODO: We can easily mark invalid states with option type? *)
  Definition step (st: state) : (state * tau) :=
    let (machine0_state', tau0) := Machine0.step st.(machine0_state) in (* throw away Core1 *)
    let (machine1_state', tau1) := Machine1.step st.(machine1_state) in (* throw away Core0 *)
    let config := st.(enclave_config) in
    let core0_config := update_core_state (config CoreId0) (tau0 CoreId0) in
    let core1_config := update_core_state (config CoreId1) (tau1 CoreId1) in
    (* If there's a context switch:
     * - copy old enclave memory into state
     * - initialise new machine with new external state, with relevant enclave data
     *)
    (* Invariant: it's never the case that we enter the same enclave *)
    (* When we are in a limbo state, we can leak and receive information about enclave status *)
    let core0_switch_opt := do_context_switch (tau0 CoreId0) (config CoreId0) (Machine0.get_dram machine0_state') in
    let core1_switch_opt := do_context_switch (tau1 CoreId1) (config CoreId1) (Machine1.get_dram machine1_state') in
    let new_config := fun id => match id with | CoreId0 => core0_config | CoreId1 => core1_config end in
    let state' :=
      match core0_switch_opt, core1_switch_opt with
      | Some switch0, Some switch1 => (* should not happen, because we time-partition enclave entry *)
          st
      | Some switch0, None =>
          let new_eid := switch0.(new_enclave) in
          let old_rf := Machine0.get_rf machine0_state' in
          let enclave_mem' := update_enclave_mem st.(enclave_mem) switch0.(old_enclave) (switch0.(old_dram)) in
          let new_dram := enclave_mem' new_eid in
               {| machine0_state := spin_up_machine0 old_rf new_eid new_dram;
                  machine1_state := update_machine1_state machine1_state' new_config;
                  enclave_config := new_config;
                  enclave_mem := enclave_mem';
                  (* shared_mem :=  *)
               |}
      | None, Some switch1 =>
          let new_eid := switch1.(new_enclave) in
          let old_rf := Machine1.get_rf machine1_state' in
          let enclave_mem' := update_enclave_mem st.(enclave_mem) switch1.(old_enclave) (switch1.(old_dram)) in
          let new_dram := enclave_mem' new_eid in
               {| machine0_state := update_machine0_state machine0_state' new_config;
                  machine1_state := spin_up_machine1 old_rf new_eid new_dram;
                  enclave_config := new_config;
                  enclave_mem := enclave_mem'
               |}
      | None, None =>
               {| machine0_state := machine0_state';
                  machine1_state := machine1_state';
                  enclave_config := fun id => match id with
                                           | CoreId0 => core0_config
                                           | CoreId1 => core1_config
                                           end;
                  enclave_mem := st.(enclave_mem)
               |}
      end in
      (state', fun id => match id with | CoreId0 => tau0 CoreId0 | CoreId1 => tau1 CoreId1 end).

  (* TODO: move to common *)

  Definition enclave_base enc_id := Bits.to_nat (EnclaveParams.enclave_base enc_id).
  Definition enclave_max enc_id := Bits.to_nat (Bits.plus (EnclaveParams.enclave_base enc_id)
                                                          (EnclaveParams.enclave_size enc_id)).

  Definition initial_enclave_config :=
    fun core_id =>
      match core_id with
      | CoreId0 => {| enclave_data := {| meta_eid := Enclave0 |};
                     in_limbo := false;
                     requested_enclave := None
                  |}
      | CoreId1 => {| enclave_data := {| meta_eid := Enclave1 |};
                     in_limbo := false;
                     requested_enclave := None
                  |}
      end.

  Section Initialised.

    Variable initial_dram : initial_dram_t.


    Definition initial_enclave_dram enc_id :=
      fun addr => if ((enclave_base enc_id) <=? addr) && (addr <? (enclave_max enc_id))
               then initial_dram addr
               else None.

    Definition initial_state : state :=
      {| machine0_state := Machine0.initial_state (initial_enclave_dram Enclave0);
         machine1_state := Machine1.initial_state (initial_enclave_dram Enclave1);
         enclave_config := initial_enclave_config;
         enclave_mem := fun eid => initial_enclave_dram eid
         (* shared_mem := option (initial_dram_t); *)
      |}.

    Fixpoint step_n (n: nat) : state * trace :=
      match n with
      | 0 => (initial_state, [])
      | S n' =>
          let (st, evs) := step_n n' in
          let (st', ev) := step st in
          (st', evs ++ [ev])
      end.

  End Initialised.

End IsolationSemantics.
