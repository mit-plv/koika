Require Import Koika.Frontend.
Require Import Coq.Lists.List.

Require Import Koika.Std.

Require Import dynamic_isolation.Interfaces.
Require Import dynamic_isolation.External.
Require Import dynamic_isolation.Framework.
Require Import dynamic_isolation.LogHelpers.
Require Import dynamic_isolation.TrivialCore.
Require Import dynamic_isolation.Tactics.

Module Common.
  Import Interfaces.Common.

  (* TODO: What's the realistic threat model? *)
  Record req_observations_t :=
    ReqObs { obs_imem_req : option (struct_t mem_req);
             obs_dmem_req : option (struct_t mem_req);
           }.

  (* TODO: We want to talk about the moment when context switching ends, but defining context switching
   *       is murky.
   *)
  Record resp_observations_t :=
    RespObs { obs_imem_resp : option (struct_t mem_resp);
              obs_dmem_resp : option (struct_t mem_resp);
            }.

  Record enc_observations_t : Type :=
    { obs_enclave_req : option (struct_t enclave_req);
      obs_enclave_enter : bool;
      obs_enclave_exit : bool 
    }.

  Record observations_t :=
    Obs { obs_reqs : req_observations_t;
          obs_resps : resp_observations_t;
          obs_encs : enc_observations_t
        }.


  Definition empty_obs_reqs : req_observations_t := {| obs_imem_req := None;
                                                       obs_dmem_req := None;
                                                    |}.
  Definition empty_obs_resps : resp_observations_t := {| obs_imem_resp := None;
                                                         obs_dmem_resp := None;
                                                      |}.

  Definition empty_obs_encs : enc_observations_t := {| obs_enclave_req := None;
                                                       obs_enclave_enter := false;
                                                       obs_enclave_exit := false 
                                                    |}.

  Definition empty_observations : observations_t :=
    {|  obs_reqs := empty_obs_reqs;
        obs_resps := empty_obs_resps;
        obs_encs := empty_obs_encs
    |}.

  Definition tau := ind_core_id -> observations_t.
  Definition local_trace := list observations_t.
  Definition trace := list tau.

  Definition dram_t : Type := nat -> option data_t.

End Common.

Module MachineSemantics (External: External_sig) (EnclaveParams: EnclaveParameters)
                        (Params0: CoreParameters) (Params1: CoreParameters)
                        (Core0: Core_sig External EnclaveParams Params0)
                        (Core1: Core_sig External EnclaveParams Params1)
                        (Memory: Memory_sig External EnclaveParams).
  Module System := Machine External EnclaveParams
                           Params0 Params1
                           Core0 Core1
                           Memory.
  Import System.
  Import Common.
  Import EnclaveInterface.

  Definition koika_state : Type := env_t ContextEnv (fun idx : reg_t => R idx).
  Definition placeholder_external_state : Type. Admitted.

  Definition state : Type := koika_state * placeholder_external_state.
  Definition log_t : Type := Log R ContextEnv.

  Definition get_dram : state -> dram_t. Admitted.
  Definition get_rf : state -> env_t ContextEnv Rf.R. Admitted.

  Definition sigma_t : Type := (forall fn: ext_fn_t, Sig_denote (Sigma fn)).
  Definition derive_sigma : placeholder_external_state -> sigma_t. Admitted.
  Definition update_ext_st: state -> placeholder_external_state. Admitted.

  Definition update_function (st: state) : Log R ContextEnv * placeholder_external_state :=
    let (koika_st, ext_st) := st in
    let sigma := derive_sigma ext_st in
    let ext_st' := update_ext_st st in
    (* TODO: really, interp_scheduler should update our external state at the same time *)
    (interp_scheduler koika_st sigma System.rules System.schedule, ext_st').

  (* Everything reset except for rf and eid *)
  (* TODO! specify core id *)
  Definition spin_up_single_core_machine
                             (core_id: ind_core_id)
                             (clk: bits_t 1)
                             (rf: env_t ContextEnv Rf.R)
                             (config: enclave_config)
                             (initial_dram: dram_t)
                             : state.
  Admitted.

  (* Replace enclave data *)
  Definition update_state_with_enclave_data (st: state) (core_id: ind_core_id) 
                                            (config: enclave_config) : state. Admitted.

  Definition empty_log : Log R ContextEnv := log_empty.

  Section Observations.
    (*
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
    *)

    Definition observe_imem_reqs0 (log: Log R ContextEnv) : option (struct_t mem_req) :=
      (observe_enq0 (System.Core0ToSM_IMem MemReq.valid0) eq_refl
                    (System.Core0ToSM_IMem MemReq.data0) eq_refl
                    log).

    Definition observe_imem_reqs1 (log: Log R ContextEnv) : option (struct_t mem_req) :=
      (observe_enq0 (System.Core1ToSM_IMem MemReq.valid0) eq_refl
                    (System.Core1ToSM_IMem MemReq.data0) eq_refl
                    log).

    (*
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
      *)

    Definition observe_imem_reqs (log: Log R ContextEnv) (core_id: ind_core_id) : option (struct_t mem_req) :=
      match core_id with
      | CoreId0 => observe_imem_reqs0 log
      | CoreId1 => observe_imem_reqs1 log
      end.

    Definition observe_dmem_reqs0 (log: Log R ContextEnv) : option (struct_t mem_req) :=
      (observe_enq0 (System.Core0ToSM_DMem MemReq.valid0) eq_refl
                    (System.Core0ToSM_DMem MemReq.data0) eq_refl
                    log).
    Definition observe_dmem_reqs1 (log: Log R ContextEnv) : option (struct_t mem_req) :=
      (observe_enq0 (System.Core1ToSM_DMem MemReq.valid0) eq_refl
                    (System.Core1ToSM_DMem MemReq.data0) eq_refl
                    log).


    (*
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
    *)

    Definition observe_dmem_reqs (log: Log R ContextEnv) (core_id: ind_core_id) : option (struct_t mem_req) :=
      match core_id with
      | CoreId0 => observe_dmem_reqs0 log
      | CoreId1 => observe_dmem_reqs1 log
      end.

    Definition observe_reqs (log: Log R ContextEnv) (core_id: ind_core_id) : req_observations_t :=
      {| obs_imem_req := observe_imem_reqs log core_id;
         obs_dmem_req := observe_dmem_reqs log core_id;
      |}.

    Definition observe_imem_resps0 (log: Log R ContextEnv) : option (struct_t mem_resp) :=
      observe_enq1 (System.SMToCore0_IMem MemResp.valid0) eq_refl
                   (System.SMToCore0_IMem MemResp.data0) eq_refl
                   log.

    Definition observe_imem_resps1 (log: Log R ContextEnv) : option (struct_t mem_resp) :=
      observe_enq1 (System.SMToCore1_IMem MemResp.valid0) eq_refl
                   (System.SMToCore1_IMem MemResp.data0) eq_refl
                   log.

    (*
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
      *)

    Definition observe_imem_resps (log: Log R ContextEnv) (core_id: ind_core_id) : option (struct_t mem_resp) :=
      match core_id with
      | CoreId0 => observe_imem_resps0 log
      | CoreId1 => observe_imem_resps1 log
      end.

    Definition observe_dmem_resps0 (log: Log R ContextEnv) : option (struct_t mem_resp) :=
      observe_enq1 (System.SMToCore0_DMem MemResp.valid0) eq_refl
                   (System.SMToCore0_DMem MemResp.data0) eq_refl
                   log.

    Definition observe_dmem_resps1 (log: Log R ContextEnv) : option (struct_t mem_resp) :=
      observe_enq1 (System.SMToCore1_DMem MemResp.valid0) eq_refl
                   (System.SMToCore1_DMem MemResp.data0) eq_refl
                   log.

    (*
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
      *)

    Definition observe_dmem_resps (log: Log R ContextEnv) (core_id: ind_core_id) : option (struct_t mem_resp) :=
      match core_id with
      | CoreId0 => observe_dmem_resps0 log
      | CoreId1 => observe_dmem_resps1 log
      end.


    Definition observe_enclave_reqs0 (log: Log R ContextEnv) : option (struct_t enclave_req) :=
      observe_enq0 (System.Core0ToSM_Enc EnclaveReq.valid0) eq_refl
                   (System.Core0ToSM_Enc EnclaveReq.data0) eq_refl
                   log.

    Definition observe_enclave_reqs1 (log: Log R ContextEnv) : option (struct_t enclave_req) :=
      observe_enq1 (System.Core1ToSM_Enc EnclaveReq.valid0) eq_refl
                   (System.Core1ToSM_Enc EnclaveReq.data0) eq_refl
                   log.

    (*
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
      *)

    Definition observe_enclave_reqs (log: Log R ContextEnv) (core_id: ind_core_id) : option (struct_t enclave_req) :=
      match core_id with
      | CoreId0 => observe_enclave_reqs0 log
      | CoreId1 => observe_enclave_reqs1 log
      end.

    Definition bits_eqb {sz} (v1: bits_t sz) (v2: bits_t sz) : bool :=
      N.eqb (Bits.to_N v1) (Bits.to_N v2).

    (* TODO (slight hack): If write reg_proc_reset == Restart, treat as switching enclaves *)
    Definition observe_enclave_enter0 (log: Log R ContextEnv) : bool :=
      match latest_write log System.purge_core0 with
      | Some v => bits_eqb v ENUM_purge_restart 
      | None => false
      end.

    Definition observe_enclave_enter1 (log: Log R ContextEnv) : bool :=
      match latest_write log System.purge_core1 with
      | Some v => bits_eqb v ENUM_purge_restart
      | None => false
      end.

    Definition observe_enclave_enters (log: Log R ContextEnv) (core_id: ind_core_id) : bool :=
      match core_id with
      | CoreId0 => observe_enclave_enter0 log
      | CoreId1 => observe_enclave_enter1 log
      end.

    Definition observe_enclave_exit0 (log: Log R ContextEnv) : bool :=
      match latest_write log (System.SM_internal System.SM.enc_data0) with
      | Some v => 
          let data := EnclaveInterface.extract_enclave_data v in
          bits_eqb (EnclaveInterface.enclave_data_valid data) Ob~0
      | None => false
      end.

    Definition observe_enclave_exit1 (log: Log R ContextEnv) : bool :=
      match latest_write log (System.SM_internal System.SM.enc_data1) with
      | Some v => 
          let data := EnclaveInterface.extract_enclave_data v in
          bits_eqb (EnclaveInterface.enclave_data_valid data) Ob~0
      | None => false
      end.

    Definition observe_enclave_exits (log: Log R ContextEnv) (core_id: ind_core_id) : bool :=
      match core_id with
      | CoreId0 => observe_enclave_exit0 log
      | CoreId1 => observe_enclave_exit1 log
      end.


    Definition observe_resps (log: Log R ContextEnv) (core_id: ind_core_id) : resp_observations_t :=
      {| obs_imem_resp := observe_imem_resps log core_id;
         obs_dmem_resp := observe_dmem_resps log core_id;
      |}.

    Definition observe_enclaves (log: Log R ContextEnv) (core_id: ind_core_id) : enc_observations_t :=
      {| obs_enclave_req := observe_enclave_reqs log core_id;
         obs_enclave_enter := observe_enclave_enters log core_id;
         obs_enclave_exit := observe_enclave_exits log core_id
      |}.


    Definition do_observations (log: Log R ContextEnv) : ind_core_id -> observations_t :=
      fun core_id => {| obs_reqs := observe_reqs log core_id;
                     obs_resps := observe_resps log core_id;
                     obs_encs := observe_enclaves log core_id
                  |}.

  End Observations.

  Definition step (st: state) : state * tau :=
    let (koika_st, ext_st) := st in
    let (log, ext_st') := update_function st in
    let obs := do_observations log in
    ((commit_update koika_st log, ext_st'), obs).

  Section Initialised.
    Variable initial_dram : dram_t.

    Definition initial_external_state : placeholder_external_state. Admitted.

    Definition initial_state : state := (ContextEnv.(create) r, initial_external_state).

    Definition step_n (n: nat) : state * trace :=
        Framework.step_n initial_state step n.

  End Initialised.

End MachineSemantics.

Module IsolationSemantics (External: External_sig) (EnclaveParams: EnclaveParameters)
                          (Params0: CoreParameters) (Params1: CoreParameters)
                          (Core0: Core_sig External EnclaveParams Params0)
                          (Core1: Core_sig External EnclaveParams Params1)
                          (Memory: Memory_sig External EnclaveParams).

  Import Interfaces.Common.
  Import EnclaveInterface.
  Import Common.

  (* TODO: core_id irrelevant *)
  Module VoidCoreParams : CoreParameters.
    Definition core_id : Common.core_id_t := Bits.zero.
    Definition initial_pc : Common.addr_t := Bits.zero.
  End VoidCoreParams.

  Module VoidCore := EmptyCore External EnclaveParams VoidCoreParams.

  Module Machine0 := MachineSemantics External EnclaveParams Params0 VoidCoreParams Core0 VoidCore Memory.
  Module Machine1 := MachineSemantics External EnclaveParams VoidCoreParams Params1 VoidCore Core1 Memory.

  Inductive enclave_state_t :=
  | EnclaveState_Running 
  | EnclaveState_Switching (next_enclave: enclave_config)
  .

  Definition enclave_req_to_eid (enclave_req: struct_t enclave_req) : option enclave_id :=
    let '(eid, _) := enclave_req in
    EnclaveInterface.bits_id_to_ind_id eid.


  Definition check_for_context_switching (obs: observations_t) : option enclave_config :=
    match obs.(obs_encs).(obs_enclave_req) with
    | Some req => 
      match enclave_req_to_eid req with
      | Some eid => 
          (* We have a valid enclave request, initiate context switching *)
          Some {| eid := eid;
                  shared_page := false; (* TODO *)
               |} 
      | None => None (* drop request *)
      end
    | None => None
    end.


  Record contextSwitchData :=
    { contextSwitch_rf : env_t ContextEnv Rf.R;
      contextSwitch_oldEnclave : enclave_config;
      contextSwitch_dram: dram_t
    }.

  (* Partitioned. *)
  Definition memory_map : Type := EnclaveInterface.mem_region -> dram_t.
  Import Interfaces.EnclaveInterface.

  Section Dram.
    Definition enclave_base enc_id := Bits.to_nat (EnclaveParams.enclave_base enc_id).
    Definition enclave_max enc_id := Bits.to_nat (Bits.plus (EnclaveParams.enclave_base enc_id)
                                                            (EnclaveParams.enclave_size enc_id)).
    Definition shared_base := Bits.to_nat EnclaveParams.shared_mem_base.
    Definition shared_max := Bits.to_nat (Bits.plus EnclaveParams.shared_mem_base EnclaveParams.shared_mem_size).

    Definition addr_in_region (region: mem_region) (addr: nat): bool :=
      match region with
      | MemRegion_Enclave eid =>
          (enclave_base eid <=? addr) && (addr <? (enclave_max eid))
      | MemRegion_Shared =>
          (shared_base <=? addr) && (addr <? shared_max)
      | MemRegion_Other => false
      end.

    Definition filter_dram : dram_t -> mem_region -> dram_t :=
      fun dram region addr =>
        if addr_in_region region addr then
          dram addr
        else None.

    (* NOTE: the current representation of memory regions is probably non-ideal... *)
    Definition get_dram : memory_map -> enclave_config -> dram_t :=
      fun mem_map enclave_config addr =>
        let enclave_region := MemRegion_Enclave enclave_config.(eid) in
        if addr_in_region enclave_region addr then
          (mem_map enclave_region) addr
        else if enclave_config.(shared_page) && (addr_in_region MemRegion_Shared addr) then
          (mem_map MemRegion_Shared) addr
        else None.

    (* Copy back relevant regions of dram *)
    Definition update_regions (config: enclave_config) (dram: dram_t)
                              (regions: memory_map)
                              : memory_map :=
      fun region =>
        if mem_region_beq region MemRegion_Shared && config.(shared_page) then
          filter_dram dram MemRegion_Shared
        else if mem_region_beq region (MemRegion_Enclave config.(eid)) then
          filter_dram dram region
        else regions region.

  End Dram.

  Scheme Equality for Common.enclave_id.

  Definition can_enter_enclave (next_enclave: enclave_config) (other_core_enclave: option enclave_config) : bool :=
    match other_core_enclave with
    | None => true
    | Some config =>
        (* Other core hasn't claimed the requested memory regions *)
        negb (enclave_id_beq next_enclave.(eid) config.(eid)) &&
        negb (next_enclave.(shared_page) && config.(shared_page))
    end.


  Section LocalStateMachine.
    Context {machine_state_t : Type}.
    Context (step_fn : machine_state_t -> machine_state_t * observations_t).
    Context (extract_rf : machine_state_t -> env_t ContextEnv Rf.R).
    Context (extract_dram: machine_state_t -> dram_t).
    Context (spin_up_machine: env_t ContextEnv Rf.R -> enclave_config -> dram_t -> machine_state_t).

    Inductive core_state_machine :=
    | CoreState_Enclave (machine_state: machine_state_t) (config: enclave_config) 
                        (enclave_state: enclave_state_t)
    | CoreState_Waiting (new: enclave_config) (next_rf: env_t ContextEnv Rf.R)
    .

    Inductive magic_state_machine :=
    | MagicState_Continue (state: core_state_machine) (obs: observations_t)
    | MagicState_Exit (waiting: enclave_config) (old_data: contextSwitchData) (obs: observations_t)
    | MagicState_TryToEnter (next_enclave: enclave_config) (next_rf: env_t ContextEnv Rf.R)
    .

    Definition get_enclave_config (st: core_state_machine) : option enclave_config :=
      match st with
      | CoreState_Enclave _ config _ => Some config 
      | _ => None
      end.
       

    Definition do_magic_step (config: magic_state_machine)
                             (mem_regions: memory_map)
                             (other_cores_enclave: option enclave_config)
                             : core_state_machine * observations_t * memory_map :=
      match config with
      | MagicState_Continue st obs => (st, obs, mem_regions) 
      | MagicState_Exit next_enclave old_data obs =>
          let new_regions := update_regions old_data.(contextSwitch_oldEnclave) 
                                            old_data.(contextSwitch_dram)
                                            mem_regions in            
          let core_state := CoreState_Waiting next_enclave old_data.(contextSwitch_rf) in
          let obs := {| obs_reqs := empty_obs_reqs;
                        obs_resps := empty_obs_resps;
                        obs_encs := {| obs_enclave_req := None;
                                       obs_enclave_enter := false;
                                       obs_enclave_exit := true
                                    |}
                     |} in
          (core_state, obs, new_regions)
      | MagicState_TryToEnter next_enclave next_rf =>
          (* Can only peek at other core's enclave when context switching *)
          if can_enter_enclave next_enclave other_cores_enclave then 
            let machine := spin_up_machine next_rf next_enclave (get_dram mem_regions next_enclave) in
            let core_state := CoreState_Enclave machine next_enclave EnclaveState_Running in
            let obs := {| obs_reqs := empty_obs_reqs;
                          obs_resps := empty_obs_resps;
                          obs_encs := {| obs_enclave_req := None;
                                         obs_enclave_enter := true;
                                         obs_enclave_exit := true
                                      |}
                       |} in
            (core_state, obs, mem_regions)
          else (CoreState_Waiting next_enclave next_rf, empty_observations, mem_regions)
      end.

    Definition local_core_step (can_switch: bool)
                               (config: core_state_machine)
                               : magic_state_machine  :=
      match config with
      | CoreState_Enclave machine enclave enclave_state =>
          (* Do a Koika step *)
          let (machine', obs) := step_fn machine in
          match enclave_state with
          | EnclaveState_Running =>
              (* Check if we want to initiate context switching *)
              let enclave_state' :=
                match check_for_context_switching obs with
                | Some next_enclave =>  EnclaveState_Switching next_enclave
                | None =>  EnclaveState_Running (* continue running the same enclave *)
                end in
              MagicState_Continue (CoreState_Enclave machine' enclave enclave_state') obs
          | EnclaveState_Switching next_enclave =>
              (* Check if we have purged all the state and can completely exit the enclave *)
              if obs.(obs_encs).(obs_enclave_exit) then
                  let context_switching_data :=
                     {| contextSwitch_rf := extract_rf machine';
                        contextSwitch_oldEnclave := enclave;
                        contextSwitch_dram := extract_dram machine'
                     |} in
                  MagicState_Exit next_enclave context_switching_data obs
              else MagicState_Continue (CoreState_Enclave machine' enclave enclave_state) obs (* Still switching *)
          end
      | CoreState_Waiting new_enclave next_rf =>
          (* Here all we can do is try to enter the enclave if it's our turn *)
          if can_switch 
          then MagicState_TryToEnter new_enclave next_rf
          else MagicState_Continue config empty_observations 
      end.

  End LocalStateMachine.

  Record state :=
    { machine0_state : @core_state_machine Machine0.state;
      machine1_state : @core_state_machine Machine1.state;
      regions : memory_map;
      clk : bool
    }.

  (* Discard Core1 observations *)
  Definition machine_step0 : Machine0.state -> Machine0.state * observations_t :=
    fun st => let '(st', tau) := Machine0.step st in (st', tau CoreId0).
  Definition machine_step1 : Machine1.state -> Machine1.state * observations_t :=
    fun st => let '(st', tau) := Machine1.step st in (st', tau CoreId1).
  
  (* Hmmm. contention with exit/enter? *)

  Definition spin_up_machine0 (rf: env_t ContextEnv Rf.R) (config: enclave_config) (dram: dram_t)
                              : Machine0.state :=
    Machine0.spin_up_single_core_machine CoreId0 Ob~1 rf config dram.

  Definition spin_up_machine1 (rf: env_t ContextEnv Rf.R) (config: enclave_config) (dram: dram_t)
                              : Machine1.state :=
    Machine1.spin_up_single_core_machine CoreId1 Ob~0 rf config dram.

  Definition step (st: state) : state * tau := 
    (* Each core independently takes a step; 
     * context switching is only allowed for core0 and core1 on even and odd cycles respectively 
     *)
    let magic0 := local_core_step machine_step0 Machine0.get_rf Machine0.get_dram (negb st.(clk)) st.(machine0_state) in
    let magic1 := local_core_step machine_step1 Machine1.get_rf Machine1.get_dram st.(clk) st.(machine1_state) in
    (* Now we allow the core to exit it's enclave region or enter a new one, if it is it's turn.
     * We should have an invariant that no core is running the same memory region, so that 
     * the order of doing the exit commutes.
     * We also enforce that you can only observe the other core's state at the start of the "previous" cycle 
     * (check security).
     *)
    let '(core0, obs0, regions') :=
        do_magic_step spin_up_machine0 magic0 st.(regions) (get_enclave_config st.(machine1_state)) in
    let '(core1, obs1, regions'') :=
        do_magic_step spin_up_machine1 magic1 regions' (get_enclave_config st.(machine0_state)) in
    let st' := {| machine0_state := core0;
                  machine1_state := core1;
                  regions := regions'';
                  clk := negb st.(clk)
               |} in
    (st', fun id => match id with | CoreId0 => obs0 | CoreId1 => obs1 end).
  
  (*
  Record context_switch_data  :=
    { old_enclave: enclave_id;
      old_dram: dram_t;
      new_enclave: enclave_id
    }.

  Definition do_context_switch (obs: observations_t) (old_config: core_config) (dram: dram_t)
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
  Definition spin_up_machine0 (rf: env_t ContextEnv Rf.R) (eid: enclave_id) (initial_dram: dram_t)
                              : Machine0.state :=
    Machine0.spin_up_machine rf eid initial_dram.

  Definition spin_up_machine1 (rf: env_t ContextEnv Rf.R) (eid: enclave_id) (initial_dram: dram_t)
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

  Definition update_enclave_mem (enclave_mem: enclave_id -> dram_t)
                                (eid: enclave_id) (dram: dram_t) : enclave_id -> dram_t :=
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
  *)


  Definition initial_enclave_config0 : enclave_config :=
    {| eid := Enclave0;
       shared_page  := false
    |}.
  Definition initial_enclave_config1 : enclave_config :=
    {| eid := Enclave1;
       shared_page  := false
    |}.

  Section Initialised.

    Context (initial_dram : dram_t).

    Definition initial_regions : memory_map :=
      fun region => filter_dram initial_dram region.

    Definition initial_state : state :=
      let machine0 := Machine0.initial_state (initial_regions (MemRegion_Enclave Enclave0)) in
      let machine1 := Machine1.initial_state (initial_regions (MemRegion_Enclave Enclave1)) in
      {| machine0_state := CoreState_Enclave machine0 initial_enclave_config0 EnclaveState_Running;
         machine1_state := CoreState_Enclave machine1 initial_enclave_config1 EnclaveState_Running;
         regions := initial_regions;
         clk := false
      |}.

    Definition step_n (n: nat) : state * trace :=
        Framework.step_n initial_state step n.

  End Initialised.

End IsolationSemantics.
