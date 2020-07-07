Require Import Koika.Frontend.
Require Import Koika.Std.

Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Import dynamic_isolation.External.
Require Import dynamic_isolation.Framework.
Require Import dynamic_isolation.Interfaces.
Require Import dynamic_isolation.Interp.
Require Import dynamic_isolation.Lift.
Require Import dynamic_isolation.LogHelpers.
Require Import dynamic_isolation.Multicore.
Require Import dynamic_isolation.Tactics.
Require Import dynamic_isolation.Util.

Set Default Goal Selector "!".

Arguments latest_write0 : simpl never.
Arguments proj_log : simpl never.
Arguments create : simpl never.
Arguments getenv : simpl never.
Arguments pf_R_equal : simpl nomatch.


Hint Rewrite @getenv_create : log_helpers.

Module TradPf (External: External_sig) (EnclaveParams: EnclaveParameters)
          (Params0: CoreParameters) (Params1: CoreParameters)
          (Core0: Core_sig External EnclaveParams Params0)
          (Core1: Core_sig External EnclaveParams Params1)
          (Memory: Memory_sig External EnclaveParams).
  Module Impl:= MachineSemantics External EnclaveParams Params0 Params1 Core0 Core1 Memory.
  Module Spec:= IsolationSemantics External EnclaveParams Params0 Params1 Core0 Core1 Memory.
  Module SM := SecurityMonitor External EnclaveParams Params0 Params1.

  Import Common.

  (* ================= TMP ====================== *)
  Definition impl_log_t : Type := Impl.log_t.

  (* ================= END_TMP ====================== *)

  Section GhostState.

    (* Experimenting with input/output state representation *)
    Inductive modules :=
    | Module_Core0
    | Module_Core1
    | Module_SM
    | Module_Memory
    .

    Record ghost_state : Type. (* TODO *)

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

  Section ImplRegisterMap.
    Definition impl_sm_clk : Impl.System.reg_t := Impl.System.SM_internal (SM_Common.clk).
    Definition impl_purge_core0 : Impl.System.reg_t := Impl.System.purge_core0.
    Definition impl_purge_core1: Impl.System.reg_t := Impl.System.purge_core1.
    Definition impl_purge_mem0 : Impl.System.reg_t := Impl.System.purge_mem0.
    Definition impl_purge_mem1 : Impl.System.reg_t := Impl.System.purge_mem1.
  End ImplRegisterMap.

  Section ImplProjs.
    Definition get_impl_core0 : Impl.koika_state_t -> Core0.state :=
      fun impl_st => proj_env Impl.System.Lift_core0 impl_st.
    Definition get_impl_core1 : Impl.koika_state_t -> Core1.state :=
      fun impl_st => proj_env Impl.System.Lift_core1 impl_st.
    Definition get_impl_sm : Impl.koika_state_t -> SM.state :=
      fun impl_st => proj_env Impl.System.Lift_sm impl_st.
    Definition get_impl_koika_mem : Impl.koika_state_t -> Memory.koika_state_t :=
      fun impl_st => proj_env Impl.System.Lift_mem impl_st.
    Definition get_impl_mem : Impl.state -> Memory.state :=
      fun impl_st => (get_impl_koika_mem (Impl.koika_state impl_st), Impl.external_state impl_st).

    Definition get_impl_log_core0 : Impl.log_t -> Log Core0.R ContextEnv :=
      fun impl_st => proj_log Impl.System.Lift_core0 impl_st.
    Definition get_impl_log_core1 : Impl.log_t -> Log Core1.R ContextEnv :=
      fun impl_st => proj_log Impl.System.Lift_core1 impl_st.
    Definition get_impl_log_sm : Impl.log_t -> Log SM_Common.R ContextEnv :=
      fun impl_st => proj_log Impl.System.Lift_sm impl_st.
    Definition get_impl_log_mem : Impl.log_t -> Log Memory.R ContextEnv :=
      fun impl_st => proj_log Impl.System.Lift_mem impl_st.

  End ImplProjs.

  Ltac unfold_get_impls :=
    unfold get_impl_core0, get_impl_core1, get_impl_sm, get_impl_mem, get_impl_koika_mem,
           get_impl_log_core0, get_impl_log_core1, get_impl_log_sm, get_impl_log_mem in *.

  Section SpecProjs.
    Definition get_spec0_core0 : Spec.Machine0.koika_state_t -> Core0.state :=
      fun spec_st => proj_env Spec.Machine0.System.Lift_core0 spec_st.
    Definition get_spec1_core1 : Spec.Machine1.koika_state_t -> Core1.state :=
      fun spec_st => proj_env Spec.Machine1.System.Lift_core1 spec_st.
    Definition get_spec0_sm : Spec.Machine0.koika_state_t -> Spec.Machine0.System.SM.state :=
      fun spec_st => proj_env Spec.Machine0.System.Lift_sm spec_st.
    Definition get_spec1_sm : Spec.Machine1.koika_state_t -> Spec.Machine1.System.SM.state :=
      fun spec_st => proj_env Spec.Machine1.System.Lift_sm spec_st.

  End SpecProjs.

  Import EnclaveInterface.

  Section Interfaces.
    (* TODO *)
    Record sm_ghost_output_t :=
      { ghost_output_config0 : option enclave_config;
        ghost_output_config1 : option enclave_config
      }.

  End Interfaces.

  (* TODO: Better name: Decoupled implementation *)
  Module ModImpl.

    Record state :=
      { state_core0 : Core0.state
      ; state_core1 : Core1.state
      ; state_sm : SM.state
      ; state_mem : Memory.state
      }.

    Record tau :=
      { output_core0 : Log Core0.R ContextEnv
      ; output_core1 : Log Core1.R ContextEnv
      ; output_sm : Log SM_Common.R ContextEnv * sm_ghost_output_t
      ; output_mem : Log Memory.R ContextEnv * Memory.external_state_t
      }.

    Definition trace := list tau.

    Section TODO_MOVE.

      Definition TODO_ghost_state_conversion (st: SM.ghost_output) : sm_ghost_output_t :=
        {| ghost_output_config0 := SM.ghost_output_config0 st;
           ghost_output_config1 := SM.ghost_output_config1 st
        |}.

    End TODO_MOVE.

    Definition initial_state (initial_dram: dram_t) : state :=
      {| state_core0 := ContextEnv.(create) Core0.r;
         state_core1 := ContextEnv.(create) Core1.r;
         state_sm := ContextEnv.(create) SM.r;
         state_mem := (ContextEnv.(create) Memory.r, Memory.initial_external_state initial_dram)
      |}.

    (* TODO: stop duplicating *)
    Section ModularStep.

      Definition do_core0 (st: Core0.state) (input_log: Log Impl.System.R ContextEnv)
                          : Log Core0.R_external ContextEnv * Log Core0.R ContextEnv *
                            Log Impl.System.R ContextEnv * Log Impl.System.R ContextEnv *
                            (Log Impl.System.R ContextEnv -> Core0.step_io) :=
        let core0_input := Core0.proj_log__ext (proj_log Impl.System.Lift_core0 input_log) in
        let '(core0_output__local, _) := Core0.do_step_input__koika st core0_input in
        let core0_output__global := lift_log (REnv' := ContextEnv) Impl.System.Lift_core0 core0_output__local in
        let acc := log_app core0_output__global input_log in
        let mk_core0_step_io feedback_log :=
            {| Core0.step_input := core0_input;
               Core0.step_feedback := Core0.proj_log__ext (proj_log Impl.System.Lift_core0 feedback_log)
            |} in
        (core0_input, core0_output__local, core0_output__global, acc, mk_core0_step_io).

      Definition do_core1 (st: Core1.state) (input_log: Log Impl.System.R ContextEnv)
                          : Log Core1.R_external ContextEnv * Log Core1.R ContextEnv *
                            Log Impl.System.R ContextEnv * Log Impl.System.R ContextEnv *
                            (Log Impl.System.R ContextEnv -> Core1.step_io) :=
        let core1_input := Core1.proj_log__ext (proj_log Impl.System.Lift_core1 input_log) in
        let '(core1_output__local, _) := Core1.do_step_input__koika st core1_input in
        let core1_output__global := lift_log (REnv' := ContextEnv) Impl.System.Lift_core1 core1_output__local in
        let acc := log_app core1_output__global input_log in
        let mk_core1_step_io feedback_log :=
            {| Core1.step_input := core1_input;
               Core1.step_feedback := Core1.proj_log__ext (proj_log Impl.System.Lift_core1 feedback_log)
            |} in
        (core1_input, core1_output__local, core1_output__global, acc, mk_core1_step_io).

      Definition do_sm (st: SM.state) (input_log: Log Impl.System.R ContextEnv)
                             : Log SM_Common.R_external ContextEnv * Log SM_Common.R ContextEnv *
                               sm_ghost_output_t * Log Impl.System.R ContextEnv * Log Impl.System.R ContextEnv *
                               (Log Impl.System.R ContextEnv -> SM.step_io) :=
        let sm_input := SM.proj_log__ext (proj_log Impl.System.Lift_sm input_log) in
        let '((sm_output__local, sm_ghost), _) := SM.do_step_input__impl st sm_input in
        let sm_output__global := lift_log (REnv' := ContextEnv) Impl.System.Lift_sm sm_output__local in
        let acc := log_app sm_output__global input_log in
        let mk_sm_step_io feedback_log :=
            {| SM.step_input := sm_input;
               SM.step_feedback := SM.proj_log__ext (proj_log Impl.System.Lift_sm feedback_log)
            |} in
        (sm_input, sm_output__local, TODO_ghost_state_conversion sm_ghost, sm_output__global, acc, mk_sm_step_io).

      Definition do_mem (st: Memory.state) (input_log: Log Impl.System.R ContextEnv)
                        : Log Memory.R_external ContextEnv * Log Memory.R ContextEnv *
                          Memory.external_state_t * Log Impl.System.R ContextEnv * Log Impl.System.R ContextEnv *
                          (Log Impl.System.R ContextEnv -> Memory.step_io) :=
        let mem_input := Memory.proj_log__ext (proj_log (REnv := ContextEnv) Impl.System.Lift_mem input_log) in
        let '(mem_output__local, ext_st) := Memory.do_step_input__impl st mem_input in
        let mem_output__global := lift_log (REnv := ContextEnv) Impl.System.Lift_mem mem_output__local in
        let acc_mem := log_app mem_output__global input_log in
        let mk_mem_step_io feedback_log :=
            {| Memory.step_input := mem_input;
               Memory.step_feedback := Memory.proj_log__ext (proj_log Impl.System.Lift_mem feedback_log)
            |} in
        (mem_input, mem_output__local, ext_st, mem_output__global, acc_mem, mk_mem_step_io).

    End ModularStep.

    (* TODO: Monad! *)
    (* TODO: fix Interfaces' do_step_input function *)
    (* TODO: Modularize *)
    Definition do_step (st: state) : state * tau :=
      (* Core0 *)
      let '(core0_input, core0_output__local, core0_output__global, acc__core0, mk_core0_step_io) :=
          do_core0 (state_core0 st) log_empty in
      (* Core1 *)
      let '(core1_input, core1_output__local, core1_output__global, acc__core1, mk_core1_step_io) :=
          do_core1 (state_core1 st) acc__core0 in
      (* SM *)
      let '(sm_input, sm_output__local, sm_ghost, sm_output__global, acc_sm, mk_sm_step_io) :=
          do_sm (state_sm st) acc__core1 in
      (* Mem *)
      let '(mem_input, mem_output__local, ext_st, mem_output__global, acc_mem, mk_mem_step_io) :=
          do_mem (state_mem st) acc_sm in
      let outputs :=
        {| output_core0 := core0_output__local;
           output_core1 := core1_output__local;
           output_sm := (sm_output__local, sm_ghost);
           output_mem := (mem_output__local, ext_st)
        |} in
      (* Do feedback: reverse *)
      let mem_feedback__global := log_empty in
      let sm_feedback__global := log_app mem_output__global mem_feedback__global in
      let core1_feedback__global := log_app sm_output__global sm_feedback__global in
      let core0_feedback__global := log_app core1_output__global core1_feedback__global in

      let core0_step_io := mk_core0_step_io core0_feedback__global in
      let core1_step_io := mk_core1_step_io core1_feedback__global in
      let sm_step_io := mk_sm_step_io sm_feedback__global in
      let mem_step_io := mk_mem_step_io mem_feedback__global in
      ({| state_core0 := fst (Core0.do_step__koika (state_core0 st) core0_step_io);
         state_core1 := fst (Core1.do_step__koika (state_core1 st) core1_step_io);
         state_sm := fst (SM.do_step__impl (state_sm st) sm_step_io);
         state_mem := fst (Memory.do_step__impl (state_mem st) mem_step_io)
       |}, outputs).

    Definition step_n (initial_dram: dram_t) (n: nat) : state * trace :=
      Framework.step_n (initial_state initial_dram) do_step n.

  End ModImpl.

  Module ModSpec.

    Record state :=
      { state_core0 : Core0.spec_state_t
      ; state_core1 : Core1.spec_state_t
      ; state_sm : SM.spec_state_t
      ; state_mem : Memory.spec_state_t
      }.

    Record tau :=
      { output_core0 : Log Core0.R ContextEnv
      ; output_core1 : Log Core1.R ContextEnv
      ; output_sm : SM.spec_output_t
      ; output_mem : Log Memory.R ContextEnv (* * Memory.external_state_t *)
      }.

    Definition trace := list tau.

    Definition initial_state (initial_dram: dram_t): state :=
      {| state_core0 := Core0.initial_spec_state;
         state_core1 := Core1.initial_spec_state;
         state_sm := SM.initial_spec_state;
         state_mem := Memory.initial_spec_state initial_dram
      |}.

    Section TODO_MOVE.

      Definition TODO_ghost_state_conversion (st: SM.ghost_output) : sm_ghost_output_t :=
        {| ghost_output_config0 := SM.ghost_output_config0 st;
           ghost_output_config1 := SM.ghost_output_config1 st
        |}.

      Definition combine_spec_output : SM.spec_output_t -> Log SM_Common.R ContextEnv * sm_ghost_output_t.
      Admitted.

      Definition combine_mem_output : Log Memory.R ContextEnv * Log Memory.R ContextEnv -> Log Memory.R ContextEnv.
      Admitted.

    End TODO_MOVE.

    (* TODO: modularize *)
    Definition do_step (st: state) : state * tau :=
      (* Core0 *)
      let '(core0_output__local, _) := Core0.do_step_trans_input__spec (state_core0 st) log_empty in
      let core0_output__global := lift_log (REnv' := ContextEnv) Impl.System.Lift_core0 core0_output__local in
      let acc__core0 := core0_output__global in
      (* Core1 *)
      let core1_input := Core1.proj_log__ext (proj_log (REnv := ContextEnv) Impl.System.Lift_core1 acc__core0) in
      let '(core1_output__local, _) := Core1.do_step_trans_input__spec (state_core1 st) core1_input in
      let core1_output__global := lift_log (REnv := ContextEnv) Impl.System.Lift_core1 core1_output__local in
      let acc__core1 := log_app core1_output__global acc__core0 in
      (* SM *)
      let sm_input := SM.proj_log__ext (proj_log (REnv := ContextEnv) Impl.System.Lift_sm acc__core1) in
      let sm_output__raw := SM.do_step_input__spec (state_sm st) sm_input in
      let '(sm_output__local, sm_ghost) := combine_spec_output sm_output__raw in
      let sm_output__global := lift_log (REnv := ContextEnv) Impl.System.Lift_sm sm_output__local in
      let acc_sm := log_app sm_output__global acc__core1 in
      (* Mem *)
      let mem_input := Memory.proj_log__ext (proj_log (REnv := ContextEnv) Impl.System.Lift_mem acc_sm) in
      let mem_output__raw := Memory.do_step_trans_input__spec (state_mem st) mem_input in
      let mem_output__local := combine_mem_output mem_output__raw in
      let mem_output__global := lift_log (REnv := ContextEnv) Impl.System.Lift_mem mem_output__local in
      let acc_mem := log_app mem_output__global acc_sm in
      let outputs :=
        {| output_core0 := core0_output__local;
           output_core1 := core1_output__local;
           output_sm := sm_output__raw;
           output_mem := mem_output__local
        |} in
      (* Do feedback: reverse *)
      let mem_feedback__global := log_empty in
      let sm_feedback__global := log_app mem_output__global mem_feedback__global in
      let core1_feedback__global := log_app sm_output__global sm_feedback__global in
      let core0_feedback__global := log_app core1_output__global core1_feedback__global in

      let core0_step_io :=
          {| Core0.step_input := log_empty;
             Core0.step_feedback := Core0.proj_log__ext (proj_log (REnv := ContextEnv) Impl.System.Lift_core0
                                                                core0_feedback__global)
          |} in
      let core1_step_io :=
          {| Core1.step_input := core1_input;
             Core1.step_feedback := Core1.proj_log__ext (proj_log Impl.System.Lift_core1 core1_feedback__global)
          |} in
      let sm_step_io :=
          {| SM.step_input := sm_input;
             SM.step_feedback := SM.proj_log__ext (proj_log Impl.System.Lift_sm sm_feedback__global)
          |} in
      let mem_step_io :=
          {| Memory.step_input := mem_input;
             Memory.step_feedback := Memory.proj_log__ext (proj_log Impl.System.Lift_mem mem_feedback__global)
          |} in
      let mem_ghost_io :=
          {| Memory.ghost_step := mem_step_io;
             Memory.ghost_input_config0 := (ghost_output_config0 sm_ghost);
             Memory.ghost_input_config1 := (ghost_output_config1 sm_ghost)
          |} in
      ({| state_core0 := fst (fst (Core0.do_step__spec (state_core0 st) core0_step_io));
         state_core1 := fst (fst (Core1.do_step__spec (state_core1 st) core1_step_io));
         state_sm := fst (fst (SM.do_step__spec (state_sm st) sm_step_io));
         state_mem := fst (fst (Memory.do_step__spec (state_mem st) mem_ghost_io))
       |}, outputs).


    Definition step_n (initial_dram: dram_t) (n: nat) : state * trace :=
      Framework.step_n (initial_state initial_dram) do_step n.

  End ModSpec.

  Module Observations.
    Import Interfaces.Common.

    (* TODO: write this in a nicer way *)
    Definition observe_imem_req0 (log: Log Core0.R ContextEnv) : option (struct_t mem_req) :=
      observe_enq0 (Core0.external (Core0.toIMem MemReq.valid0)) eq_refl
                   (Core0.external (Core0.toIMem MemReq.data0)) eq_refl log.
    Definition observe_dmem_req0 (log: Log Core0.R ContextEnv) : option (struct_t mem_req) :=
      observe_enq0 (Core0.external (Core0.toDMem MemReq.valid0)) eq_refl
                   (Core0.external (Core0.toDMem MemReq.data0)) eq_refl log.
    Definition observe_imem_req1 (log: Log Core1.R ContextEnv) : option (struct_t mem_req) :=
      observe_enq0 (Core1.external (Core1.toIMem MemReq.valid0)) eq_refl
                   (Core1.external (Core1.toIMem MemReq.data0)) eq_refl log.
    Definition observe_dmem_req1 (log: Log Core1.R ContextEnv) : option (struct_t mem_req) :=
      observe_enq0 (Core1.external (Core1.toDMem MemReq.valid0)) eq_refl
                   (Core1.external (Core1.toDMem MemReq.data0)) eq_refl log.
    Definition observe_imem_resp0 (log: Log SM_Common.R ContextEnv) : option (struct_t mem_resp) :=
      observe_enq1 (SM_Common.external (SM_Common.toCore0_IMem MemResp.valid0)) eq_refl
                   (SM_Common.external (SM_Common.toCore0_IMem MemResp.data0)) eq_refl log.
    Definition observe_dmem_resp0 (log: Log SM_Common.R ContextEnv) : option (struct_t mem_resp) :=
      observe_enq1 (SM_Common.external (SM_Common.toCore0_DMem MemResp.valid0)) eq_refl
                   (SM_Common.external (SM_Common.toCore0_DMem MemResp.data0)) eq_refl log.
    Definition observe_imem_resp1 (log: Log SM_Common.R ContextEnv) : option (struct_t mem_resp) :=
      observe_enq1 (SM_Common.external (SM_Common.toCore1_IMem MemResp.valid0)) eq_refl
                   (SM_Common.external (SM_Common.toCore1_IMem MemResp.data0)) eq_refl log.
    Definition observe_dmem_resp1 (log: Log SM_Common.R ContextEnv) : option (struct_t mem_resp) :=
      observe_enq1 (SM_Common.external (SM_Common.toCore1_DMem MemResp.valid0)) eq_refl
                   (SM_Common.external (SM_Common.toCore1_DMem MemResp.data0)) eq_refl log.
    Definition observe_enclave_req0 (log: Log Core0.R ContextEnv) : option (struct_t enclave_req) :=
      observe_enq0 (Core0.external (Core0.toSMEnc EnclaveReq.valid0)) eq_refl
                   (Core0.external (Core0.toSMEnc EnclaveReq.data0)) eq_refl
                   log.
    Definition observe_enclave_req1 (log: Log Core1.R ContextEnv) : option (struct_t enclave_req) :=
      observe_enq0 (Core1.external (Core1.toSMEnc EnclaveReq.valid0)) eq_refl
                   (Core1.external (Core1.toSMEnc EnclaveReq.data0)) eq_refl
                   log.
    Definition observe_enclave_enter0 (log: Log SM_Common.R ContextEnv) : bool :=
      match latest_write log (SM_Common.external SM_Common.purge_core0) with
      | Some v => bits_eqb v ENUM_purge_restart
      | None => false
      end.
    Definition observe_enclave_enter1 (log: Log SM_Common.R ContextEnv) : bool :=
      match latest_write log (SM_Common.external SM_Common.purge_core1) with
      | Some v => bits_eqb v ENUM_purge_restart
      | None => false
      end.
    Definition observe_enclave_exit0 (log: Log SM_Common.R ContextEnv) : bool :=
      match latest_write log (SM_Common.internal SM_Common.enc_data0) with
      | Some v =>
          let data := EnclaveInterface.extract_enclave_data v in
          bits_eqb (EnclaveInterface.enclave_data_valid data) Ob~0
      | None => false
      end.
    Definition observe_enclave_exit1 (log: Log SM_Common.R ContextEnv) : bool :=
      match latest_write log (SM_Common.internal SM_Common.enc_data1) with
      | Some v =>
          let data := EnclaveInterface.extract_enclave_data v in
          bits_eqb (EnclaveInterface.enclave_data_valid data) Ob~0
      | None => false
      end.

    Definition generate_observations__modImpl (ev: ModImpl.tau) : tau :=
      fun core_id =>
        let sm_output := fst (ModImpl.output_sm ev) in
        let core0_output := ModImpl.output_core0 ev in
        let core1_output := ModImpl.output_core1 ev in
        match core_id with
        | CoreId0 =>
            {| obs_reqs := {| obs_imem_req := observe_imem_req0 (core0_output);
                              obs_dmem_req := observe_dmem_req0 (core0_output)
                           |};
               obs_resps := {| obs_imem_resp := observe_imem_resp0 (sm_output);
                               obs_dmem_resp := observe_dmem_resp0 (sm_output)
                            |};
               obs_encs := {| obs_enclave_req := observe_enclave_req0 (core0_output);
                              obs_enclave_enter := observe_enclave_enter0 (sm_output);
                              obs_enclave_exit := observe_enclave_exit0 (sm_output)
                           |}
            |}
        | CoreId1 =>
            {| obs_reqs := {| obs_imem_req := observe_imem_req1 (core1_output);
                              obs_dmem_req := observe_dmem_req1 (core1_output)
                           |};
               obs_resps := {| obs_imem_resp := observe_imem_resp1 (sm_output);
                               obs_dmem_resp := observe_dmem_resp1 (sm_output)
                            |};
               obs_encs := {| obs_enclave_req := observe_enclave_req1 (core1_output);
                              obs_enclave_enter := observe_enclave_enter1 (sm_output);
                              obs_enclave_exit := observe_enclave_exit1 (sm_output)
                           |}
           |}
        end.

    Definition generate_observations__modSpec (ev: ModSpec.tau) : tau :=
      fun core_id =>
        let sm0_output := fst (fst (ModSpec.output_sm ev)) in
        let sm1_output := fst (snd (ModSpec.output_sm ev)) in
        let core0_output := ModSpec.output_core0 ev in
        let core1_output := ModSpec.output_core1 ev in
        match core_id with
        | CoreId0 =>
            {| obs_reqs := {| obs_imem_req := observe_imem_req0 (core0_output);
                              obs_dmem_req := observe_dmem_req0 (core0_output)
                           |};
               obs_resps := {| obs_imem_resp := observe_imem_resp0 (sm0_output);
                               obs_dmem_resp := observe_dmem_resp0 (sm0_output)
                            |};
               obs_encs := {| obs_enclave_req := observe_enclave_req0 (core0_output);
                              obs_enclave_enter := observe_enclave_enter0 (sm0_output);
                              obs_enclave_exit := observe_enclave_exit0 (sm0_output)
                           |}
            |}
        | CoreId1 =>
            {| obs_reqs := {| obs_imem_req := observe_imem_req1 (core1_output);
                              obs_dmem_req := observe_dmem_req1 (core1_output)
                           |};
               obs_resps := {| obs_imem_resp := observe_imem_resp1 (sm1_output);
                               obs_dmem_resp := observe_dmem_resp1 (sm1_output)
                            |};
               obs_encs := {| obs_enclave_req := observe_enclave_req1 (core1_output);
                              obs_enclave_enter := observe_enclave_enter1 (sm1_output);
                              obs_enclave_exit := observe_enclave_exit1 (sm1_output)
                           |}
           |}
        end.

    Ltac unfold_mod_impl_obs :=
      unfold observe_imem_req0, observe_imem_req1,
             observe_dmem_req0, observe_dmem_req1,
             observe_imem_resp0, observe_imem_resp1,
             observe_dmem_resp0, observe_dmem_resp1,
             observe_enclave_req0, observe_enclave_req1,
             observe_enclave_enter0, observe_enclave_enter0,
             observe_enclave_exit0, observe_enclave_exit1
             in *.

    (* TODO_MOVE *)
    Ltac unfold_impl_obs :=
      unfold Impl.observe_reqs, Impl.observe_resps, Impl.observe_enclaves,
             Impl.observe_imem_reqs, Impl.observe_imem_reqs0, Impl.observe_imem_reqs1,
             Impl.observe_dmem_reqs, Impl.observe_dmem_reqs0, Impl.observe_dmem_reqs1,
             Impl.observe_imem_resps, Impl.observe_imem_resps0, Impl.observe_imem_resps1,
             Impl.observe_dmem_resps, Impl.observe_dmem_resps0, Impl.observe_dmem_resps1,
             Impl.observe_enclave_reqs, Impl.observe_enclave_reqs0, Impl.observe_enclave_reqs1,
             Impl.observe_enclave_exits, Impl.observe_enclave_exit0, Impl.observe_enclave_exit1,
             Impl.observe_enclave_exits, Impl.observe_enclave_exit0, Impl.observe_enclave_exit1
             in *.
  End Observations.


  Module ImplToModImpl.
    Import Observations.
    Import Interfaces.Common.

    Section GeneralizeImpl.
      Definition gen_impl_tau : Type := Log Impl.System.R ContextEnv * Impl.placeholder_external_state.
      Definition gen_impl_trace := list gen_impl_tau.
      Definition gen_impl_step (st: Impl.state) : Impl.state * gen_impl_tau :=
        let (log, ext_st') := Impl.update_function st in
        (Impl.MkState (commit_update (Impl.koika_state st) log) ext_st', (log, ext_st')).
      Definition gen_impl_step_n (dram: dram_t) (n: nat) : Impl.state * gen_impl_trace :=
        Framework.step_n (Impl.initial_state dram) gen_impl_step n.
    End GeneralizeImpl.

    Section Simulation.
      (* TODO: inductive vs relation? *)
      (* TODO: eventually we'll need a log equality definition *)

      Inductive Sim (impl_st: Impl.state) (mod_st: ModImpl.state) : Type :=
      | _Sim:
          forall (core0_sim: get_impl_core0 (Impl.koika_state impl_st) = ModImpl.state_core0 mod_st)
            (core1_sim: get_impl_core1 (Impl.koika_state impl_st) = ModImpl.state_core1 mod_st)
            (sm_sim: get_impl_sm (Impl.koika_state impl_st) = ModImpl.state_sm mod_st)
            (mem_sim: get_impl_mem impl_st = ModImpl.state_mem mod_st),
          Sim impl_st mod_st.

      Inductive GenTauSim (gen_ev: gen_impl_tau) (mod_ev: ModImpl.tau) :=
      | _GenTauSim :
          forall (core0_sim: get_impl_log_core0 (fst gen_ev) = ModImpl.output_core0 mod_ev)
            (core1_sim: get_impl_log_core1 (fst gen_ev) = ModImpl.output_core1 mod_ev)
            (sm_sim: get_impl_log_sm (fst gen_ev) = fst (ModImpl.output_sm mod_ev))
            (mem_log_sim : get_impl_log_mem (fst gen_ev) = fst (ModImpl.output_mem mod_ev))
            (mem_ext_st_sm : snd gen_ev = snd (ModImpl.output_mem mod_ev)),
          GenTauSim gen_ev mod_ev.

      Definition GenTraceSim (gen_tr: gen_impl_trace) (mod_tr: ModImpl.trace) : Prop :=
        Forall2 GenTauSim gen_tr mod_tr.

      Local Hint Constructors Sim : core.
      Local Hint Constructors GenTauSim : core.
      Local Hint Unfold GenTraceSim : core.


Ltac destruct_one_ind :=
  match goal with
  | [ H: ?T |- _ ] => is_ind T; destruct H
  end.
Ltac destruct_inds := repeat destruct_one_ind.

Lemma wf_r_lift_core0:
  forall k,
  rew [fun t : type => t] pf_R_equal Impl.System.Lift_core0 k in Impl.System.r (rlift Impl.System.Lift_core0 k) =
  Core0.r k.
Proof.
  intros; destruct_inds; auto.
Qed.

Lemma wf_r_lift_core1:
  forall k,
  rew [fun t : type => t] pf_R_equal Impl.System.Lift_core1 k in Impl.System.r (rlift Impl.System.Lift_core1 k) =
  Core1.r k.
Proof.
  intros; destruct_inds; auto.
Qed.

Lemma wf_r_lift_sm:
  forall k,
  rew [fun t : type => t] pf_R_equal Impl.System.Lift_sm k in Impl.System.r (rlift Impl.System.Lift_sm k) =
  SM.r k.
Proof.
  intros; destruct_inds; auto.
Qed.

Lemma wf_r_lift_mem:
  forall k,
  rew [fun t : type => t] pf_R_equal Impl.System.Lift_mem k in Impl.System.r (rlift Impl.System.Lift_mem k) =
  Memory.r k.
Proof.
  intros; destruct_inds; auto.
Qed.


Local Hint Resolve wf_r_lift_core0 : core.
Local Hint Resolve wf_r_lift_core1 : core.
Local Hint Resolve wf_r_lift_sm : core.
Local Hint Resolve wf_r_lift_mem : core.

      Lemma initial_state_sim (initial_dram: dram_t):
        Sim (Impl.initial_state initial_dram) (ModImpl.initial_state initial_dram).
      Proof.
        constructor; simpl; unfold_get_impls.
        4: apply f_equal2; auto.
        all: apply equiv_eq; unfold equiv, proj_env; intros;
             repeat (autorewrite with log_helpers; simpl; auto).
      Qed.

      Theorem step_sim : forall (impl_st impl_st': Impl.state) (mod_st mod_st': ModImpl.state)
                           (impl_ev: gen_impl_tau) (mod_ev: ModImpl.tau),
        Sim impl_st mod_st ->
        gen_impl_step impl_st = (impl_st', impl_ev) ->
        ModImpl.do_step mod_st = (mod_st', mod_ev) ->
        Sim impl_st' mod_st' /\ GenTauSim impl_ev mod_ev.
      Proof.
      Admitted.

      Theorem step_n_sim :
        forall (initial_dram: dram_t) (n: nat)
          (gen_st: Impl.state) (gen_tr: gen_impl_trace)
          (mod_st: ModImpl.state) (mod_tr: ModImpl.trace),
          gen_impl_step_n initial_dram n = (gen_st, gen_tr) ->
          ModImpl.step_n initial_dram n = (mod_st, mod_tr) ->
          Sim gen_st mod_st /\ GenTraceSim gen_tr mod_tr.
      Proof.
        induction n; simpl; intros; simplify_tuples; subst; auto.
        - intuition. apply initial_state_sim.
        - destruct_all_matches; simplify_tuples; subst; auto.
          specialize IHn with (1 := eq_refl) (2 := eq_refl); propositional.
          specialize step_sim with (1 := IHn0) (2 := Heqp2) (3 := Heqp0); intuition.
          apply Forall2_app; auto.
      Qed.

    End Simulation.

    Section GenToImpl.
      Definition genToImpl_tau_related (impl_tau: tau) (gen_tau: gen_impl_tau) :=
        impl_tau = Impl.do_observations (fst gen_tau).

      Definition genToImpl_trace_related (impl_tr: trace) (gen_tr: gen_impl_trace) :=
        Forall2 genToImpl_tau_related impl_tr gen_tr.

      Local Hint Unfold genToImpl_tau_related : core.
      Local Hint Unfold genToImpl_trace_related : core.

      Theorem genToImpl_refinement :
        forall (initial_dram: dram_t) (n: nat)
          (gen_st: Impl.state) (gen_tr: gen_impl_trace)
          (impl_st: Impl.state) (impl_tr: trace),
          Impl.step_n initial_dram n = (impl_st, impl_tr) ->
          gen_impl_step_n initial_dram n = (gen_st, gen_tr) ->
          impl_st = gen_st /\ genToImpl_trace_related impl_tr gen_tr.
      Proof.
        induction n; simpl; intros; simplify_tuples; subst; auto.
        destruct_all_matches; simplify_tuples; subst.
        specialize IHn with (1 := eq_refl) (2 := eq_refl); propositional.
        unfold gen_impl_step, Impl.step in *.
        destruct_all_matches; simplify_tuples; subst.
        split; auto.
        apply Forall2_app; auto.
      Qed.

    End GenToImpl.

    Section TopLevel.

      Definition tau_related : tau -> ModImpl.tau -> Prop :=
        fun impl_ev mod_ev =>
          impl_ev = generate_observations__modImpl mod_ev.

      Definition trace_related : trace -> ModImpl.trace -> Prop :=
        fun impl_tr mod_tr => List.Forall2 tau_related impl_tr mod_tr.

      Local Hint Unfold tau_related : core.
      Local Hint Unfold trace_related : core.

      Lemma chain_tau_implication :
        forall impl_tau gen_tau mod_tau,
        genToImpl_tau_related impl_tau gen_tau ->
        GenTauSim gen_tau mod_tau ->
        tau_related impl_tau mod_tau.
      Proof.
        intros.
        unfold genToImpl_tau_related, tau_related in *; subst.
        unfold generate_observations__modImpl.
        unfold Impl.do_observations in *.
        apply functional_extensionality.
        destruct H0; subst.
        unfold_impl_obs; unfold_mod_impl_obs; unfold_fifo_obs; unfold_get_impls.
        destruct x; auto;
          try rewrite<-core0_sim; try rewrite<-core1_sim; try rewrite<-sm_sim;
          repeat apply f_equal3;
          repeat (autorewrite with log_helpers; autounfold with log_helpers); auto.
      Qed.

      Lemma chain_trace_implication :
        forall impl_tr gen_tr mod_tr,
        genToImpl_trace_related impl_tr gen_tr ->
        GenTraceSim gen_tr mod_tr ->
        trace_related impl_tr mod_tr.
      Proof.
        unfold genToImpl_trace_related, GenTraceSim, trace_related.
        intros.
        apply Forall2_compose with (2 := H) (3 := H0).
        apply chain_tau_implication.
      Qed.

      Theorem refinement :
        forall (initial_dram: dram_t) (n: nat)
          (impl_st: Impl.state) (impl_tr: trace)
          (mod_st: ModImpl.state) (mod_tr: ModImpl.trace),
        Impl.step_n initial_dram n = (impl_st, impl_tr) ->
        ModImpl.step_n initial_dram n = (mod_st, mod_tr) ->
        trace_related impl_tr mod_tr.
      Proof.
        intros.
        destruct_with_eqn (gen_impl_step_n initial_dram n).
        eapply chain_trace_implication with (gen_tr := g).
        - eapply genToImpl_refinement; eauto.
        - eapply step_n_sim; eauto.
      Qed.

    End TopLevel.

  End ImplToModImpl.

  Module ModImplToModSpec.
    Import Observations.
    Definition tau_related : ModImpl.tau -> ModSpec.tau -> Prop :=
      fun impl_ev spec_ev =>
      generate_observations__modImpl impl_ev = generate_observations__modSpec spec_ev.

    Definition trace_related : ModImpl.trace -> ModSpec.trace -> Prop :=
      fun impl_tr spec_tr => List.Forall2 tau_related impl_tr spec_tr.

    Theorem refinement :
      forall (initial_dram: dram_t) (n: nat)
        (impl_st: ModImpl.state) (impl_tr: ModImpl.trace)
        (spec_st: ModSpec.state) (spec_tr: ModSpec.trace),
      ModImpl.step_n initial_dram n = (impl_st, impl_tr) ->
      ModSpec.step_n initial_dram n = (spec_st, spec_tr) ->
      trace_related impl_tr spec_tr.
    Proof.
    Admitted.

  End ModImplToModSpec.

  Module ModSpecToSpec.
    Import Observations.
    Import Interfaces.Common.

    Definition tau_related :  ModSpec.tau -> tau -> Prop :=
      fun mod_ev spec_ev =>
      generate_observations__modSpec mod_ev = spec_ev.

    Definition trace_related : ModSpec.trace -> trace -> Prop :=
      fun mod_tr spec_tr => List.Forall2 tau_related mod_tr spec_tr.

    Theorem refinement :
      forall (initial_dram: dram_t) (n: nat)
        (mod_st: ModSpec.state) (mod_tr: ModSpec.trace)
        (spec_st: Spec.state) (spec_tr: trace),
      ModSpec.step_n initial_dram n = (mod_st, mod_tr) ->
      Spec.step_n initial_dram n = (spec_st, spec_tr) ->
      trace_related mod_tr spec_tr.
    Proof.
    Admitted.

  End ModSpecToSpec.

  Section TopLevel.
    Context (initial_dram: dram_t).

    Theorem chain_trace_equivalence :
      forall (impl_tr: trace) (impl_mod_tr: ModImpl.trace)
        (spec_mod_tr: ModSpec.trace) (spec_tr: trace),
      ImplToModImpl.trace_related impl_tr impl_mod_tr ->
      ModImplToModSpec.trace_related impl_mod_tr spec_mod_tr ->
      ModSpecToSpec.trace_related spec_mod_tr spec_tr ->
      impl_tr = spec_tr.
    Proof.
      intros.
      apply Forall2_eq.
      eapply Forall2_compose with (2 := H).
      2: { apply Forall2_compose with (2 := H0) (3 := H1).
           unfold ModImplToModSpec.tau_related.
           unfold ModSpecToSpec.tau_related.
           Unshelve.
           2 : exact (fun x z => Observations.generate_observations__modImpl x = z).
           intuition.
         }
      intuition. unfold ImplToModImpl.tau_related in *.
      intuition.
    Qed.

    Theorem top_level_refinement:
        forall (n: nat)
          (impl_st: Impl.state) (impl_tr: trace)
          (spec_st: Spec.state) (spec_tr: trace),
        Impl.step_n initial_dram n = (impl_st, impl_tr) ->
        Spec.step_n initial_dram n = (spec_st, spec_tr) ->
        impl_tr = spec_tr.
    Proof.
      intros *; intros HStepImpl HStepSpec.
      destruct (ModImpl.step_n initial_dram n) eqn:?.
      destruct (ModSpec.step_n initial_dram n) eqn:?.
      eapply chain_trace_equivalence.
      - eapply ImplToModImpl.refinement; eauto.
      - eapply ModImplToModSpec.refinement; eauto.
      - eapply ModSpecToSpec.refinement; eauto.
    Qed.

  End TopLevel.


  (* ============== DEPRECATED ================== *)


  Section Modularspec.
    Record mod_step_tau_t :=
      { mod_core0_output : Log Core0.R ContextEnv
      ; mod_core1_output : Log Core1.R ContextEnv
      ; sm_output__spec
      }.

  End ModularSpec.

  Section Modular.
    Record mod_step :=
      { apres_core0: Log Impl.System.R ContextEnv;
        apres_core1: Log Impl.System.R ContextEnv;
        apres_sm   : Log Impl.System.R ContextEnv * sm_ghost_output_t;
        final_log : Log Impl.System.R ContextEnv;
        final_ext_state: Impl.placeholder_external_state
      }.

    (* TODO: (fancy?) notation *)
    (* TODO:
     * > Spec State
     * > Modular spec state
     * > Modular impl state
     * > Impl
     *)

    (* TODO: generalize *)
    Definition TODO_ghost_state_conversion (st: Impl.System.SM.ghost_output) : sm_ghost_output_t :=
      {| ghost_output_config0 := Impl.System.SM.ghost_output_config0 st;
         ghost_output_config1 := Impl.System.SM.ghost_output_config1 st
      |}.

    Definition do_core0_step (st: Core0.state) (input_log: Log Impl.System.R ContextEnv)
                             : Log Impl.System.R ContextEnv :=
      let core0_log := proj_log (REnv := ContextEnv) Impl.System.Lift_core0 input_log in
      let output_log := Core0.update_function st core0_log in
      lift_log (REnv := ContextEnv) Impl.System.Lift_core0 output_log.

    Definition do_core1_step (st: Core1.state) (input_log: Log Impl.System.R ContextEnv)
                             : Log Impl.System.R ContextEnv :=
      let core1_log := proj_log (REnv := ContextEnv) Impl.System.Lift_core1 input_log in
      let output_log := Core1.update_function st core1_log in
      lift_log (REnv := ContextEnv) Impl.System.Lift_core1 output_log.

    Definition do_sm_step (st: Impl.System.SM.state) (input_log: Log Impl.System.R ContextEnv)
                          : Log Impl.System.R ContextEnv * sm_ghost_output_t :=
      let sm_log := proj_log (REnv := ContextEnv) Impl.System.Lift_sm input_log in
      let '(output_log, sm_ghost_output) := Impl.System.SM.update_function st sm_log in
      (lift_log (REnv := ContextEnv) Impl.System.Lift_sm output_log, TODO_ghost_state_conversion sm_ghost_output).

    Definition do_mem_step (st: Memory.state) (input_log: Log Impl.System.R ContextEnv)
                          : Log Impl.System.R ContextEnv * Impl.placeholder_external_state :=
      let mem_log := proj_log (REnv := ContextEnv) Impl.System.Lift_mem input_log in
      let '(output_log, ext_st') := Memory.update_function st mem_log in
      (lift_log (REnv' := ContextEnv) Impl.System.Lift_mem output_log, ext_st').

    Definition get_mod_step__impl (impl_st: Impl.state) : mod_step :=
      let koika_st := Impl.koika_state impl_st in
      let apres_core0_log := do_core0_step (get_impl_core0 koika_st) log_empty in
      let apres_core1_log := do_core1_step (get_impl_core1 koika_st) apres_core0_log in
      (* SM *)
      let sm_input := log_app apres_core1_log apres_core0_log in
      let (apres_sm_log, sm_ghost_output) := do_sm_step (get_impl_sm koika_st) sm_input in
      (* Mem *)
      let mem_input := log_app apres_sm_log sm_input in
      let (apres_mem_log, ext_st') := do_mem_step (get_impl_mem impl_st) mem_input in
      let final := log_app apres_mem_log mem_input in
      {| apres_core0 := apres_core0_log;
         apres_core1 := apres_core1_log;
         apres_sm := (apres_sm_log, sm_ghost_output);
         final_log := final;
         final_ext_state := ext_st'
      |}.

    Definition do_mod_step__impl (impl_st: Impl.state) (step: mod_step) : Impl.state :=
      {| Impl.koika_state := commit_update (Impl.koika_state impl_st) (final_log step);
         Impl.external_state := final_ext_state step
      |}.

    Fixpoint get_mod_steps__impl (initial_dram: dram_t) (n: nat) : Impl.state * list mod_step :=
      match n with
      | 0 => (Impl.initial_state initial_dram, [])
      | S n' =>
          let '(st, steps) := get_mod_steps__impl initial_dram n' in
          let mod_step := get_mod_step__impl st in
          (do_mod_step__impl st mod_step, steps ++ [mod_step])
      end.

    Definition mod_spec_st : Type. Admitted.
    Definition mod_spec_tr : Type. Admitted.

    Definition do_mod_steps__spec (initial_dram: dram_t) (steps: list mod_step)
                                : mod_spec_st * mod_spec_tr.
    Admitted.

  End Modular.

  (* TODO: this is just the standard layers. Can write as a framework later *)
  Section ImplToModularImpl.

    Definition impl_to_mod_impl_trace_equivalent : trace -> list mod_step -> Prop.
    Admitted.

    Lemma impl_to_mod_impl_refinement :
      forall (initial_dram: dram_t) (n: nat)
        (impl_st: Impl.state) (impl_tr: trace)
        (mod_st: Impl.state) (mod_steps: list mod_step),
        Impl.step_n initial_dram n = (impl_st, impl_tr) ->
        get_mod_steps__impl initial_dram n = (mod_st, mod_steps) ->
        impl_to_mod_impl_trace_equivalent impl_tr mod_steps.
    Admitted.

  End ImplToModularImpl.

  Section ModularImplToModularSpec.
    Definition mod_impl_to_mod_spec_trace_equivalent : list mod_step -> mod_spec_tr -> Prop.
    Admitted.


    Lemma mod_impl_to_mod_spec_refinement :
      forall (initial_dram: dram_t) (n: nat)
        (impl_st: Impl.state) (mod_steps: list mod_step)
        (spec_st: mod_spec_st) (spec_tr: mod_spec_tr),
        get_mod_steps__impl initial_dram n = (impl_st, mod_steps) ->
        do_mod_steps__spec initial_dram mod_steps = (spec_st, spec_tr) ->
        mod_impl_to_mod_spec_trace_equivalent mod_steps spec_tr.
    Proof.
    Admitted.

  End ModularImplToModularSpec.

  Section ModularSpecToSpec.
    Lemma mod_spec_to_spec_refinement :
      forall (initial_dram: dram_t) (n: nat)
        (mod_st: mod_spec_st) (mod_tr: mod_spec_tr)
        (spec_st: Spec.state) (spec_tr: trace),
        ?get_mod_steps__impl initial_dram n = (impl_st, mod_steps) ->
        Spec.step_n initial_dram n = (spec_st, spec_tr) ->


  End ModularSpecToSpec.

  Section Initialised.
    Context (initial_dram : dram_t).

    (* Proof idea:
     * - reduce steps to input/output to individual modules, then use the modular proofs to do the lift
     * - The modular proofs give us trace equivalence of the input/output effects of the impl and spec.
     * - Need to show that impl_step_n <-> do_steps and similarly for spec
     * - traces produced are the same implies we get trace equivalence!
     *)
    Lemma refinement': forall (n: nat)
                          (impl_st: Impl.state) (impl_tr: trace)
                          (spec_st: Spec.state) (spec_tr: trace),
        Impl.step_n initial_dram n = (impl_st, impl_tr) ->
        Spec.step_n initial_dram n = (spec_st, spec_tr) ->
        impl_tr = spec_tr.
    Proof.
    Admitted.


    Theorem refinement: forall (n: nat)
                          (impl_st: Impl.state) (impl_tr: trace)
                          (spec_st: Spec.state) (spec_tr: trace),
        Impl.step_n initial_dram n = (impl_st, impl_tr) ->
        Spec.step_n initial_dram n = (spec_st, spec_tr) ->
        impl_tr = spec_tr.
    Proof.






(* ============================================================================ *)






  Definition impl_state_t : Type := Impl.state * impl_ghost_state.
  Definition spec_state_t : Type := Spec.state * spec_ghost_state.

  Definition SpecInvariant0 (spec_core: @Spec.core_state_machine Spec.Machine0.state) : Prop :=
    match spec_core with
    | Spec.CoreState_Enclave _ _ _ => True (* TODO *)
    | Spec.CoreState_Waiting new next_rf => True
    end.

  Definition SpecInvariant : spec_state_t -> Prop. Admitted.

  (* TODO: very WIP; maybe an explicit ghost state will be better *)
  Definition State0_Sim : Impl.state -> @Spec.core_state_machine Spec.Machine0.state -> Prop :=
    fun '(impl_st, impl_ext) spec_core =>
    match spec_core with
    | Spec.CoreState_Enclave machine_state config enclave_state =>
        (* Machine state simulation: *)
        (* 1) Core0 is in the same state *)
        get_impl_core0 impl_st = get_spec0_core0 machine_state /\
        (* 2) Mem0 is in the same state, or we've had the same history of requests from a reset state?
         *    Note: this might be better stated as a ghost-state property; TBD
         *)
        (* 3) SM? *)
        (* enclave state *)
        match enclave_state with
        | Spec.EnclaveState_Running =>
          True
        | Spec.EnclaveState_Switching next => True
        end
    | Spec.CoreState_Waiting new next_rf =>
        (* Core0 is in a reset state *)
        Core0.valid_reset_state (get_impl_core0 impl_st) /\
        (* Core0 is purged *)
        ContextEnv.(getenv) impl_st impl_purge_mem0 = Common.ENUM_purge_purged /\
        (* Mem0 is in a reset state *)
        Memory.valid_reset_state (get_impl_mem impl_st) Common.CoreId0 /\
        (* Mem0 is purged *)
        ContextEnv.(getenv) impl_st impl_purge_mem0 = Common.ENUM_purge_purged /\
        (* Rf is related *)
        Impl.get_rf (impl_st,impl_ext) = next_rf /\
        (* SM is in a certain state *)
        SMProperties.valid_waiting_state (get_impl_sm impl_st) Common.CoreId0 new
        (* TODO: External memory is related *)
    end.

  Definition State1_Sim : Impl.state -> @Spec.core_state_machine Spec.Machine1.state -> Prop. Admitted.

  Definition Clk_Sim : Impl.state -> bool -> Prop :=
    fun '(impl_st, _) spec_clk =>
      let impl_clk := getenv ContextEnv impl_st impl_sm_clk in
      Bits.single impl_clk = spec_clk.

  Definition StateSim : Impl.state -> Spec.state -> Prop :=
    fun impl_st spec_st =>
      State0_Sim impl_st (Spec.machine0_state spec_st) /\
      State1_Sim impl_st (Spec.machine1_state spec_st) /\
      Clk_Sim impl_st (Spec.clk spec_st).
      (* TODO: Mem_Sim *)

  Definition Sim (impl: impl_state_t) (spec: spec_state_t) : Prop :=
    let (impl_st, impl_ghost) := impl in
    let (spec_st, spec_ghost) := spec in
    StateSim impl_st spec_st.

  Section Initialised.
    Variable initial_dram: dram_t.

    Theorem initial_state_sim :
      Sim (Impl.initial_state initial_dram, initial_impl_ghost)
          (Spec.initial_state initial_dram, initial_spec_ghost).
    Admitted.

Ltac initialize :=
  intros; unfold impl_state_t, spec_state_t in *; repeat destruct_pair.

    Theorem step_sim : forall (impl_st impl_st': impl_state_t) (spec_st spec_st': spec_state_t)
                         (impl_tau spec_tau: tau),
      Sim impl_st spec_st ->
      impl_step_with_ghost impl_st = (impl_st', impl_tau) ->
      spec_step_with_ghost spec_st = (spec_st', spec_tau) ->
      Sim impl_st' spec_st' /\ impl_tau = spec_tau.
    Proof.
      initialize.
      unfold impl_step_with_ghost, Impl.step in *.
      unfold spec_step_with_ghost, Spec.step in *.
      destruct_all_matches.
      simplify_all.

      unfold Impl.do_observations.
      unfold Spec.do_magic_step in Heqp.
      destruct_outer_match_in_hyp Heqp; simplify_tuples; subst.

      { (* Case1: MagicState_Continue *)
        unfold Spec.local_core_step in Heqm1.
        destruct_outer_match_in_hyp Heqm1.
        { (* Case: Spec.CoreState_Enclave *)
          destruct_outer_match_in_hyp Heqm1.
          (* TODO: Machine step invariant: show preservation *)
          destruct_outer_match_in_hyp Heqm1.
          { (* Case: Spec.EnclaveState_Running *)
            (* Invariant preservation, log preservation *)
            admit.
          }
          { destruct_ite_in_hyp Heqm1; try congruence.
            (* Case: Spec.EnclaveState_Switching; no exit *)
            inversion_clear Heqm1.
            (* Invariant preservation *)
          admit.
          }
        }
        { destruct_ite_in_hyp Heqm1; try congruence.
          (* Case: Spec.CoreState_Waiting; no switch *)
          inversion_clear Heqm1.
          (* Idea: Spec.clk spec_st0 = true ->
             Core0 still in reset and Mem0 still in reset *)
          (* Therefore no update to logs, therefore empty observations *)
          admit.
        }
      }
      { (* Case2: Spec.MagicState_Exit *)
        unfold Spec.local_core_step in Heqm1.
        repeat destruct_matches_in_hyp Heqm1; try congruence.
        inversion_clear Heqm1.
        (* Idea: Simulation in terms of SM; prove that Impl step exits too *)
        admit.
      }
      { (* Case3: Spec.MagicState_Enter *)
        destruct_ite_in_hyp Heqp.
        { (* Case: Spec.can_enter *)
          simplify_all.
          (* Initial enclave simulation: Impl enters enclave too *)
          admit.
        }
        { (* Case: Spec can not enter; no change *)
          simplify_all.
          admit.
        }
      }
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

(* DEPRECATED *)
(*
  Module SMProperties.
    Include Interfaces.Common.
    Include Interfaces.EnclaveInterface.
    Include Impl.System.SM.

    Section Semantics.
      Definition empty_log : Log R ContextEnv := log_empty.
      Parameter update_function : state -> Log R ContextEnv -> Log R ContextEnv.
        (* Except without the append *)
        (* interp_scheduler' st ? rules log scheduler. *)

      (* Output intermediate log *)
      Definition step (st: state) (input: Log R ContextEnv) (feedback: Log R ContextEnv)
                      : state * Log R ContextEnv :=
        let output := update_function st input in
        (commit_update st (log_app feedback (log_app output input)), output).

    End Semantics.

    Section LogHelpers.
      Definition update_no_writes_to_reg (st: state) (log: Log R ContextEnv) (reg: reg_t) : Prop :=
        latest_write (update_function st log) reg = latest_write log reg.

    End LogHelpers.

    Import EnclaveInterface.

    Section IsolatedSystem.

      Inductive enclave_state_t :=
      | EnclaveState_Running 
      | EnclaveState_Switching (next_enclave: enclave_config)
      .

      Inductive sm_state_machine :=
      | SmState_Enclave (machine_state: state) (config: enclave_config) 
                        (enclave_state: enclave_state_t)
      | SmState_Waiting (new: enclave_config).

      Inductive sm_magic_state_machine :=
      | SmMagicState_Continue (st: sm_state_machine) (ext: Log R ContextEnv)
      | SmMagicState_Exit (waiting: enclave_config) (ext: Log R ContextEnv)
      | SmMagicState_TryToEnter (next_enclave: enclave_config). 

      Record iso_machine_t :=
        { iso_sm0 : sm_state_machine;
          iso_sm1 : sm_state_machine;
          turn : bool
        }.

      Inductive taint_t :=
      | TaintCore (core_id: ind_core_id)
      | Bottom.

      Definition internal_reg_to_taint (reg: internal_reg_t) : taint_t :=
        match reg with
        | state0 => TaintCore CoreId0
        | state1 => TaintCore CoreId1
        | enc_data0 => TaintCore CoreId0
        | enc_data1 => TaintCore CoreId1
        | enc_req0 => TaintCore CoreId0
        | enc_req1 => TaintCore CoreId1
        | clk => Bottom
        end.

      Definition reg_to_taint (reg: reg_t) : taint_t :=
        match reg with
        | fromCore0_IMem st => TaintCore CoreId0
        | fromCore0_DMem st => TaintCore CoreId0
        | fromCore0_Enc st => TaintCore CoreId0
        | toCore0_IMem st => TaintCore CoreId0
        | toCore0_DMem st => TaintCore CoreId0
        (* Core1 <-> SM *)
        | fromCore1_IMem st => TaintCore CoreId1
        | fromCore1_DMem st => TaintCore CoreId1
        | fromCore1_Enc st => TaintCore CoreId1
        | toCore1_IMem st => TaintCore CoreId1
        | toCore1_DMem st => TaintCore CoreId1
        (* SM <-> Mem *)
        | toMem0_IMem st => TaintCore CoreId0
        | toMem0_DMem st => TaintCore CoreId0
        | toMem1_IMem st => TaintCore CoreId1
        | toMem1_DMem st => TaintCore CoreId1
        | fromMem0_IMem st => TaintCore CoreId0
        | fromMem0_DMem st => TaintCore CoreId0
        | fromMem1_IMem st => TaintCore CoreId1
        | fromMem1_DMem st => TaintCore CoreId1
        | pc_core0 => TaintCore CoreId0
        | pc_core1 => TaintCore CoreId1
        | purge_core0 => TaintCore CoreId0
        | purge_core1 => TaintCore CoreId1
        | purge_mem0 => TaintCore CoreId0
        | purge_mem1 => TaintCore CoreId1
        | internal st => internal_reg_to_taint st
      end.
      
      Scheme Equality for taint_t.

      Definition filter_external (log: Log R ContextEnv) (core: ind_core_id) : Log R ContextEnv :=
        ContextEnv.(create) (fun r => match r with
                                   | internal s => []
                                   | reg => if (taint_t_beq (reg_to_taint reg) (TaintCore core))
                                              || (taint_t_beq (reg_to_taint reg) Bottom) then
                                              ContextEnv.(getenv) log reg
                                           else []
                                   end).

      Definition check_for_context_switching (core_id: ind_core_id) (input_log: Log R ContextEnv) 
                                             : option EnclaveInterface.enclave_config.
      Admitted.

      Definition bits_eqb {sz} (v1: bits_t sz) (v2: bits_t sz) : bool :=
        N.eqb (Bits.to_N v1) (Bits.to_N v2).

      (* TODO: normal way of writing this? *)
      Definition observe_enclave_exit (core_id: ind_core_id) (log: Log R ContextEnv) : bool.
        refine(
        let enc_data_reg := match core_id with
                            | CoreId0 => internal enc_data0 
                            | CoreId1 => internal enc_data1
                            end in
        match rew_latest_write log enc_data_reg _ with
        | Some v =>
            let data := EnclaveInterface.extract_enclave_data v in
            bits_eqb (EnclaveInterface.enclave_data_valid data) Ob~0
        | None => false
        end).
        - destruct core_id; reflexivity.
      Defined.

      Definition local_core_step (can_switch: bool) (core_id: ind_core_id)
                                 (config: sm_state_machine) (input: Log R ContextEnv) (feedback: Log R ContextEnv)
                                 : sm_magic_state_machine * Prop * Prop :=
        let TODO_valid_input := True in
        let TODO_valid_feedback := True in
        let st :=
          match config with
          | SmState_Enclave machine enclave enclave_state =>
              let (machine', output_log) := step machine input feedback in
              (* let output_log := filter_external *)
              match enclave_state with
              | EnclaveState_Running =>
                  let enclave_state' :=
                    match check_for_context_switching core_id input with
                    | Some next_enclave => EnclaveState_Switching next_enclave
                    | None => EnclaveState_Running
                    end in
                  SmMagicState_Continue (SmState_Enclave machine' enclave enclave_state') output_log
              | EnclaveState_Switching next_enclave =>
                  if observe_enclave_exit core_id output_log 
                  then SmMagicState_Exit next_enclave output_log
                  else SmMagicState_Continue (SmState_Enclave machine' enclave enclave_state) output_log
              end 
          | SmState_Waiting next_enclave =>
              if can_switch
              then SmMagicState_TryToEnter next_enclave
              else SmMagicState_Continue config empty_log
          end in
        (st, TODO_valid_input, TODO_valid_feedback).

      Definition can_enter_enclave (next_enclave: enclave_config) (other_core_enclave: option enclave_config) : bool :=
        match other_core_enclave with
        | None => true
        | Some config =>
            (* Other core hasn't claimed the requested memory regions *)
            negb (enclave_id_beq next_enclave.(eid) config.(eid)) &&
            negb (next_enclave.(shared_page) && config.(shared_page))
        end.

      Definition enclave_config_to_enclave_data (config: enclave_config) : struct_t enclave_data :=
        mk_enclave_data {| enclave_data_eid := enclave_id_to_bits config.(eid);
                           enclave_data_addr_min := EnclaveParams.enclave_base config.(eid);
                           enclave_data_size := EnclaveParams.enclave_size config.(eid);
                           enclave_data_shared_page := if config.(shared_page) then Ob~1 else Ob~0;
                           enclave_data_valid := Ob~1
                        |}.

      Definition TODO_spin_up_machine (core: ind_core_id) (next: enclave_config) (turn: bool) : state :=
        ContextEnv.(create) (fun reg => match reg return R reg with
                                   | internal enc_data0 => 
                                       if ind_core_id_beq core CoreId0 
                                       then enclave_config_to_enclave_data next
                                       else r (internal enc_data0)
                                   | internal enc_data1 => 
                                       if ind_core_id_beq core CoreId1
                                       then enclave_config_to_enclave_data next
                                       else r (internal enc_data1)
                                   | internal clk => if turn then Ob~1 else Ob~0
                                   | reg' => r reg'
                                   end).
                                   
      Definition do_magic_step (core: ind_core_id)
                               (turn: bool)
                               (config: sm_magic_state_machine)
                               (other_cores_enclave: option enclave_config)
                               : sm_state_machine * Log R ContextEnv :=
        match config with
        | SmMagicState_Continue st obs => (st, obs)
        | SmMagicState_Exit next_enclave obs =>
           (SmState_Waiting next_enclave, obs)
        | SmMagicState_TryToEnter next_enclave =>
            if can_enter_enclave next_enclave other_cores_enclave then
              let machine := TODO_spin_up_machine core next_enclave turn in
              let sm_state := SmState_Enclave machine next_enclave EnclaveState_Running in
              let obs := empty_log in (* TODO *)
              (sm_state, obs)
             else (SmState_Waiting next_enclave, empty_log)
        end.

      Definition get_enclave_config (st: sm_state_machine) : option enclave_config :=
        match st with
        | SmState_Enclave _ config _ => Some config 
        | _ => None
        end.

      Definition iso_step (st: iso_machine_t) (input: Log R ContextEnv) (feedback: Log R ContextEnv) 
                          : iso_machine_t * (Log R ContextEnv * Log R ContextEnv) :=
        let magic0 := local_core_step (negb st.(turn)) CoreId0 st.(iso_sm0) 
                                      (filter_external input CoreId0) (filter_external feedback CoreId0) in
        let magic1 := local_core_step st.(turn) CoreId1 st.(iso_sm1) 
                                      (filter_external input CoreId1) (filter_external feedback CoreId1) in
        let '(iso0', log0) := do_magic_step CoreId0 (negb st.(turn)) magic0 (get_enclave_config st.(iso_sm1)) in
        let '(iso1', log1) := do_magic_step CoreId1 (negb st.(turn)) magic1 (get_enclave_config st.(iso_sm0)) in
        let st' := {| iso_sm0 := iso0';
                      iso_sm1 := iso1';
                      turn := negb st.(turn)
                   |} in
        (st', (log0, log1)). (* TODO: process log0 and log1 *)

    End IsolatedSystem.

    Section ValidInput.
      (* Input log is valid iff
       * - only touches interface/external registers
       * - only enqueues/dequeues to relevant FIFOs
       * - any write to purge_core is well-behaved as per purge state machine model
       *)
      (* Feedback log is similarly valid as above. Not very interesting *)
      (* Valid output is a function of state:
       * - We want to say the output addresses belong to disjoint taints in a sense, but we can derive this.
       * - Also enough to say that the outputs belong to the enclave, 
       *)

      Definition valid_input_log (st: state) (log: Log R ContextEnv) : Prop. Admitted.
      Definition valid_input_state (st: state) : Prop. Admitted.
      Definition valid_feedback_log : state -> Log R ContextEnv -> Log R ContextEnv -> Prop. Admitted.
    End ValidInput.

    Section Correctness.
      Theorem correctness:
 

    End Correctness.

    Section Compliance.

    End Compliance.


      Inductive taint_t :=
      | TaintCore (core_id: ind_core_id)
      | Bottom.

      (* More generic framework:
       * time partition based on contents of a register, which is deterministic.
       * So function from time to taint.
       * Idea is that equivalence holds as an independent function of time?;
       * Note: SM is entirely spatially partitioned. Normally this would need to be a function of time too
       *)
      Definition internal_reg_to_taint (reg: internal_reg_t) : taint_t :=
        match reg with
        | state0 => TaintCore CoreId0
        | state1 => TaintCore CoreId1
        | enc_data0 => TaintCore CoreId0
        | enc_data1 => TaintCore CoreId1
        | enc_req0 => TaintCore CoreId0
        | enc_req1 => TaintCore CoreId1
        | clk => Bottom
        end.

      Definition reg_to_taint (reg: reg_t) : taint_t :=
        match reg with
        | fromCore0_IMem st => TaintCore CoreId0
        | fromCore0_DMem st => TaintCore CoreId0
        | fromCore0_Enc st => TaintCore CoreId0
        | toCore0_IMem st => TaintCore CoreId0
        | toCore0_DMem st => TaintCore CoreId0
        (* Core1 <-> SM *)
        | fromCore1_IMem st => TaintCore CoreId1
        | fromCore1_DMem st => TaintCore CoreId1
        | fromCore1_Enc st => TaintCore CoreId1
        | toCore1_IMem st => TaintCore CoreId1
        | toCore1_DMem st => TaintCore CoreId1
        (* SM <-> Mem *)
        | toMem0_IMem st => TaintCore CoreId0
        | toMem0_DMem st => TaintCore CoreId0
        | toMem1_IMem st => TaintCore CoreId1
        | toMem1_DMem st => TaintCore CoreId1
        | fromMem0_IMem st => TaintCore CoreId0
        | fromMem0_DMem st => TaintCore CoreId0
        | fromMem1_IMem st => TaintCore CoreId1
        | fromMem1_DMem st => TaintCore CoreId1
        | pc_core0 => TaintCore CoreId0
        | pc_core1 => TaintCore CoreId1
        | purge_core0 => TaintCore CoreId0
        | purge_core1 => TaintCore CoreId1
        | purge_mem0 => TaintCore CoreId0
        | purge_mem1 => TaintCore CoreId1
        | internal st => internal_reg_to_taint st
      end.

    End ValidInput.

    Section Initialise.

      Definition internal_waiting_state (eid_req0: option enclave_id) (eid_req1: option enclave_id)
                                        (clk: bits_t 1) (idx: internal_reg_t) : R_internal idx :=
        match idx with
        | state0 => ENUM_CORESTATE_WAITING
        | state1 => ENUM_CORESTATE_WAITING
        | enc_data0 => value_of_bits (Bits.zero)
        | enc_data1 => value_of_bits (Bits.zero)
        | enc_req0 => 
           match eid_req0 with
           | Some id => eid_to_initial_enclave_data id
           | None => value_of_bits Bits.zero
           end
        | enc_req1 => 
           match eid_req1 with
           | Some id => eid_to_initial_enclave_data id
           | None => value_of_bits Bits.zero
           end
        | clk => clk
        end.

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

      Definition initialise_waiting_r (eid_req0: option enclave_id) (eid_req1: option enclave_id)
                                      (clk: bits_t 1) (idx: reg_t) : R idx :=
        match idx with
        | internal s => internal_waiting_state eid_req0 eid_req1 clk s
        | s => r s
        end. 

      Definition initialise_with_eid (eid0: option enclave_id) (eid1: option enclave_id) 
                                     (clk: bits_t 1) (idx: reg_t) : R idx :=
        match idx with
        | internal s => initialise_internal_with_eid eid0 eid1 clk s
        | s => r s
        end.

    End Initialise.

    Section ValidResetState.
      (* TODO: clk ignored *)
      Definition valid_waiting_state (st: state) (core_id: ind_core_id)  
                                     (next: EnclaveInterface.enclave_config) : Prop :=
        forall reg, reg_to_taint reg = TaintCore core_id ->
               (reg <> pc_core0 /\ reg <> pc_core1) ->
               match core_id with
               | CoreId0 => initialise_waiting_r (Some next.(EnclaveInterface.eid)) None Ob~0 reg 
                           = ContextEnv.(getenv) st reg
               | CoreId1 => initialise_waiting_r None (Some next.(EnclaveInterface.eid)) Ob~0 reg
                           = ContextEnv.(getenv) st reg
               end.

      (* TODO: not quite complete. *)
      Definition valid_reset_state (st: state) (core_id: ind_core_id) (eid: enclave_id): Prop :=
        forall reg, reg_to_taint reg = TaintCore core_id ->
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
            enclave_data.(enclave_data_addr_min) = EnclaveParams.enclave_base id /\
            enclave_data.(enclave_data_size) = EnclaveParams.enclave_size id
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
        forall r, reg_to_taint r = TaintCore core_id ->
             ContextEnv.(getenv) log1 r = ContextEnv.(getenv) log2 r.

      Definition equiv_log_at_shared (log1: Log R ContextEnv) (log2: Log R ContextEnv) : Prop :=
        forall r, reg_to_taint r = Bottom ->
             ContextEnv.(getenv) log1 r = ContextEnv.(getenv) log2 r.

      Definition equiv_log_for_core (core_id: ind_core_id) (log1: Log R ContextEnv) (log2: Log R ContextEnv) : Prop :=
        equiv_log_at_core core_id log1 log2 /\ equiv_log_at_shared log1 log2.

      Definition equiv_st_at_core (core_id: ind_core_id) (st1: state) (st2: state) : Prop :=
        forall r, reg_to_taint r = TaintCore core_id ->
             ContextEnv.(getenv) st1 r = ContextEnv.(getenv) st2 r.

      Definition equiv_st_at_shared (st1: state) (st2: state) : Prop :=
        forall r, reg_to_taint r = Bottom ->
             ContextEnv.(getenv) st1 r = ContextEnv.(getenv) st2 r.

      Definition equiv_st_for_core (core_id: ind_core_id) (st1: state) (st2: state) : Prop :=
        equiv_st_at_core core_id st1 st2 /\ equiv_st_at_shared st1 st2.

      (* Assuming we are not initially in a limbo state, output is a function only of taint0 registers *)
      Definition output_is_a_function_of_partitioned_registers:
        forall (core_id: ind_core_id) (st0 st1: state) (log0 log1: Log R ContextEnv),
        state_eq st0 core_id (value_of_bits Bits.zero) ->
        valid_input_state st0 ->
        valid_input_state st1 ->
        valid_input_log st0 log0 ->
        valid_input_log st1 log1 ->
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
        | toMem1_DMem MemReq.valid0 =>
            core_id = CoreId1 /\
            latest_write log (toMem1_DMem MemReq.valid0) <> Some Ob~1
        | _ => False
        end.

      (* TODO: rephrase this. This is annoying to work with *)
      Definition no_external_enqs (core_id: ind_core_id) (st: state) (log: Log R ContextEnv) : Prop :=
        forall reg, no_enq_to_output_reg core_id reg (update_function st log) \/
               update_no_writes_to_reg st log reg.

    End SMInternalAxioms.

    (* TODO: this needs to be in a framework *)
    Section CycleModel.
      Record step_params :=
        { param_input : Log R ContextEnv;
          param_feedback: Log R ContextEnv -> Log R ContextEnv
        }.

      Definition prop_holds_about_sm_step (st: state) (params: step_params)
                                          (P: state -> Log R ContextEnv -> Log R ContextEnv -> Log R ContextEnv -> Prop) : Prop :=
        let update := update_function st params.(param_input) in
        let final := params.(param_feedback) update in
        P st params.(param_input) update final.

      (* Given a valid input state and input log, for any state' log' that are related,
       * the output log is the same.
       *)
      Definition P_partition (core_id: ind_core_id)
                 (st: state) (input_log output_log feedback_log: Log R ContextEnv) : Prop :=
        forall st' log',
        (*
        valid_input_state st' ->
        valid_input_log st log' ->
        *)
        equiv_st_for_core core_id st st' ->
        equiv_log_for_core core_id input_log log' ->
        equiv_log_for_core core_id output_log (update_function st' log').

      Definition do_step (st: state) (input_log: Log R ContextEnv)
                         (feedback_fn: Log R ContextEnv -> Log R ContextEnv) :=
        let update := update_function st input_log in
        let final := feedback_fn update in
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

      (* TODO: restructure *)
      Definition observe_enclave_reqs (log: Log R ContextEnv) (core_id: ind_core_id) : option (struct_t enclave_req).
      Admitted.

      Definition valid_enclave_req (req: struct_t enclave_req) : Prop :=
        let '(eid, _) := req in
        Bits.to_nat eid < 4.

      Definition P_no_enclave_req (core_id: ind_core_id)
                                  : state -> Log R ContextEnv -> Log R ContextEnv -> Log R ContextEnv -> Prop :=
        fun st input_log output_log _ =>
          match observe_enclave_reqs output_log core_id with
          | None => True
          | Some req => not (valid_enclave_req req)
          end.

      Definition observe_imem_reqs_to_mem0 (log: Log R ContextEnv) : option (struct_t mem_req) :=
        observe_enq0 (toMem0_IMem MemReq.valid0) eq_refl
                     (toMem0_IMem MemReq.data0) eq_refl
                     log.

      Definition observe_imem_reqs_to_mem1 (log: Log R ContextEnv) : option (struct_t mem_req) :=
        observe_enq0 (toMem1_IMem MemReq.valid0) eq_refl
                     (toMem1_IMem MemReq.data0) eq_refl
                     log.

      Definition observe_imem_reqs_to_mem (log: Log R ContextEnv) (core_id: ind_core_id) : option (struct_t mem_req) :=
        match core_id with
        | CoreId0 => observe_imem_reqs_to_mem0 log
        | CoreId1 => observe_imem_reqs_to_mem1 log
        end.

      Definition observe_dmem_reqs_to_mem0 (log: Log R ContextEnv) : option (struct_t mem_req) :=
        observe_enq0 (toMem0_DMem MemReq.valid0) eq_refl
                     (toMem0_DMem MemReq.data0) eq_refl
                     log.

      Definition observe_dmem_reqs_to_mem1 (log: Log R ContextEnv) : option (struct_t mem_req) :=
        observe_enq0 (toMem1_DMem MemReq.valid0) eq_refl
                     (toMem1_DMem MemReq.data0) eq_refl
                     log.

      Definition observe_dmem_reqs_to_mem (log: Log R ContextEnv) (core_id: ind_core_id) : option (struct_t mem_req) :=
        match core_id with
        | CoreId0 => observe_dmem_reqs_to_mem0 log
        | CoreId1 => observe_dmem_reqs_to_mem1 log
        end.

      Definition P_mem_reqs_in_range (mem: ind_cache_type) (core_id: ind_core_id) (eid: enclave_id)
                                     : state -> Log R ContextEnv -> Log R ContextEnv -> Log R ContextEnv -> Prop :=
        let addr_min := EnclaveParams.enclave_base eid in
        let addr_max := Bits.plus (EnclaveParams.enclave_base eid) (EnclaveParams.enclave_size eid) in
        fun st input_log output_log _ =>
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


      Fixpoint prop_holds_for_sm_steps (steps: list step_params) (st: state) 
                                       (P: state -> Log R ContextEnv -> Log R ContextEnv -> Log R ContextEnv -> Prop) : Prop :=
        match steps with
        | [] => True
        | step :: steps =>
          let state' := do_step st step.(param_input) step.(param_feedback) in
          prop_holds_about_sm_step st step P /\
          prop_holds_for_sm_steps steps state' P
        end.

      Fixpoint valid_steps (st: state) (steps: list step_params) : Prop :=
        match steps with
        | [] => valid_input_state st
        | step :: steps =>
            let update := update_function st step.(param_input) in
            let final := step.(param_feedback) update in
            let state' := commit_update st final in
            valid_input_log st step.(param_input) /\
            valid_feedback_log st step.(param_input) final /\
            valid_input_state state' /\
            valid_steps state' steps
        end.

      (* If the core starts out in a limbo state, we say there are no valid writes to the outside world *)
      Theorem limbo_implies_no_external_enqs:
        forall (core_id: ind_core_id) (st: state) (log: Log R ContextEnv),
        not (state_eq st core_id (value_of_bits Bits.zero)) ->
        valid_input_state st ->
        valid_input_log st log ->
        no_external_enqs core_id st log.
      Proof.
      Admitted.

      (* The proof itself is simpler, something like "output_is_a_function_of_partitioned_registers" *)
      (* TODO: need to include mention of shared state *)
      Theorem partitioned_when_in_reset_state:
        forall (core_id: ind_core_id) (st: state) (eid: enclave_id),
        valid_reset_state st core_id eid ->
        forall (steps: list step_params),
        valid_steps st steps ->
        prop_holds_for_sm_steps steps st (P_no_enclave_req core_id) ->
        prop_holds_for_sm_steps steps st (P_partition core_id).
      Admitted.

      Theorem reqs_to_enclave_memory_in_range:
        forall (core_id: ind_core_id) (st: state) (eid: enclave_id),
        valid_reset_state st core_id eid ->
        forall (steps: list step_params),
        valid_steps st steps ->
        prop_holds_for_sm_steps steps st (P_no_enclave_req core_id) ->
        prop_holds_for_sm_steps steps st (P_mem_reqs_in_range CacheType_Imem core_id eid) /\
        prop_holds_for_sm_steps steps st (P_mem_reqs_in_range CacheType_Dmem core_id eid).
      Admitted.

      (* TODO: mention we are back in a reset state *)

      (*
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
        let addr_min := EnclaveParams.enclave_base eid in
        let addr_max := Bits.plus (EnclaveParams.enclave_base eid) (EnclaveParams.enclave_size eid) in
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
      *)
    End CycleModel.

      
  End SMProperties.
*)
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

(* TODO: move this *)

