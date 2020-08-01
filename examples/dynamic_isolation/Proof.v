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
Arguments lift_log : simpl never.
Arguments proj_log : simpl never.
Arguments proj_env : simpl never.
Arguments create : simpl never.
Arguments getenv : simpl never.
Arguments pf_R_equal : simpl nomatch.
Arguments log_empty : simpl never.
Arguments log_app : simpl never.
Arguments interp_scheduler' : simpl never.
Arguments commit_update : simpl never.
Arguments lift_scheduler : simpl never.
Arguments Log : simpl never.

Declare Scope log_scope.
Delimit Scope log_scope with log.
Infix "++" := log_app (right associativity, at level 60) : log_scope.



Hint Rewrite @getenv_create : log_helpers.


Module TradPf (External: External_sig) (EnclaveParams: EnclaveParameters)
          (Params0: CoreParameters) (Params1: CoreParameters)
          (Core0: Core_sig External EnclaveParams Params0)
          (Core1: Core_sig External EnclaveParams Params1)
          (Memory: Memory_sig External EnclaveParams).
  Module Impl:= MachineSemantics External EnclaveParams Params0 Params1 Core0 Core1 Memory.
  Module Spec:= IsolationSemantics External EnclaveParams Params0 Params1 Core0 Core1 Memory.
  (* Deduplicate *)
  Module TODO_SM := SecurityMonitor External EnclaveParams Params0 Params1.

  Import Interfaces.Common.

(* TODO_MOVE *)
Ltac destruct_one_var_with t :=
  match goal with
  | [ H: ?T |- _ ] => is_var H; destruct H; try t
  end.
Ltac destruct_vars_with t :=
  repeat (destruct_one_var_with t).

Ltac solve' :=
  match goal with
  | |- ?x = (fst ?x, snd ?x) =>
    destruct x; reflexivity
  | [ H: False |- _ ] => solve [ destruct H ]
  | [ H: ?P |- ?P ] => exact H
  end.

Ltac rewrite_in_goal :=
  repeat lazymatch goal with
  | H: ?x = ?x |- _ =>  fail 1
  | H: ?x = _ |- context[?x] =>
      rewrite H
  end.

Ltac simplify_tupless := simplify_tuples; subst.


Tactic Notation "destruct_one_var" := destruct_one_var_with auto.
Tactic Notation "destruct_vars_with" tactic(t) := repeat (destruct_one_var_with t).
Tactic Notation "destruct_vars" := destruct_vars_with auto.

  Section TODO_WF_Properties.
    Property wf_r_lift_core0:
      forall k,
      rew [fun t : type => t] pf_R_equal Impl.System.Lift_core0 k in
          Impl.System.r (rlift Impl.System.Lift_core0 k) =
      Core0.r k.
    Proof.
      intros; destruct_vars; auto.
    Qed.

    Property wf_r_lift_core1:
      forall k,
      rew [fun t : type => t] pf_R_equal Impl.System.Lift_core1 k in Impl.System.r (rlift Impl.System.Lift_core1 k) =
      Core1.r k.
    Proof.
      intros; destruct_vars; auto.
    Qed.

    Property wf_r_lift_sm:
      forall k,
      rew [fun t : type => t] pf_R_equal Impl.System.Lift_sm k in Impl.System.r (rlift Impl.System.Lift_sm k) =
      Impl.System.SM.r k.
    Proof.
      intros; destruct_vars; auto.
    Qed.

    Property wf_r_lift_mem:
      forall k,
      rew [fun t : type => t] pf_R_equal Impl.System.Lift_mem k in Impl.System.r (rlift Impl.System.Lift_mem k) =
      Memory.r k.
    Proof.
      intros; destruct_vars; auto.
    Qed.

    Property wf_core0_Sigma :
      forall f, Impl.System.Sigma (Impl.System.FnLift_id.(rlift) f) = Core0.Sigma f.
    Proof.
      auto.
    Qed.

    Property wf_core0_sigma :
     forall f : (_ext_fn_t External.ext),
       Core0.sigma f =
         rew [fun e : ExternalSignature => Sig_denote e] pf_R_equal Impl.System.FnLift_id f in
         Impl.System.sigma (rlift Impl.System.FnLift_id f).
    Proof.
      auto.
    Qed.

    Lemma wf_core1_Sigma :
      forall f, Impl.System.Sigma (Impl.System.FnLift_id.(rlift) f) = Core1.Sigma f.
    Proof.
      auto.
    Qed.

    Lemma wf_core1_sigma :
     forall f : (_ext_fn_t External.ext),
       Core1.sigma f =
         rew [fun e : ExternalSignature => Sig_denote e] pf_R_equal Impl.System.FnLift_id f in
         Impl.System.sigma (rlift Impl.System.FnLift_id f).
    Proof.
      auto.
    Qed.

    Definition core0_empty_private_regs (log: Log Core0.R ContextEnv) :=
      (forall private_reg, ContextEnv.(getenv) log (Core_Common.private private_reg) = []).
    Definition core1_empty_private_regs (log: Log Core1.R ContextEnv) :=
      (forall private_reg, ContextEnv.(getenv) log (Core_Common.private private_reg) = []).

    Definition sm_empty_private_regs (log: Log SM_Common.R ContextEnv) :=
      (forall private_reg, ContextEnv.(getenv) log (SM_Common.private private_reg) = []).

    Definition mem_empty_private_regs (log: Log Memory.R ContextEnv) :=
      (forall private_reg, ContextEnv.(getenv) log (Mem_Common.private private_reg) = []).

    Property core0_lift_ext_log_cancels_proj:
      forall log,
      core0_empty_private_regs log ->
      Core_Common.lift_ext_log (Core_Common.proj_log__pub log) = log.
    Proof.
      unfold core0_empty_private_regs; intros.
      unfold Core_Common.lift_ext_log, Core_Common.proj_log__pub.
      apply_equiv_eq.
      destruct k; auto_with_log_helpers.
    Qed.

    Property core1_lift_ext_log_cancels_proj:
      forall log,
      core1_empty_private_regs log ->
      Core_Common.lift_ext_log (Core_Common.proj_log__pub log) = log.
    Proof.
      unfold core1_empty_private_regs; intros.
      unfold Core_Common.lift_ext_log, Core_Common.proj_log__pub.
      apply_equiv_eq.
      destruct k; auto_with_log_helpers.
    Qed.

    Property sm_lift_ext_log_cancels_proj:
      forall log,
      sm_empty_private_regs log ->
      SM_Common.lift_ext_log (SM_Common.proj_log__pub log) = log.
    Proof.
      unfold sm_empty_private_regs; intros.
      unfold SM_Common.lift_ext_log, SM_Common.proj_log__pub.
      apply_equiv_eq.
      destruct k; auto_with_log_helpers.
    Qed.

    Property mem_lift_ext_log_cancels_proj:
      forall log,
      mem_empty_private_regs log ->
      Mem_Common.lift_ext_log (Mem_Common.proj_log__pub log) = log.
    Proof.
      unfold sm_empty_private_regs; intros.
      unfold Mem_Common.lift_ext_log, Mem_Common.proj_log__pub.
      apply_equiv_eq.
      destruct k; auto_with_log_helpers.
    Qed.

    Property equivalent_rules_core0_lift :
      forall sched,
      equivalent_rules
         (lift_rule Impl.System.Lift_core0 Impl.System.FnLift_id)
         (lift_scheduler Core0.rules sched)
         Impl.System.rules
         (lift_scheduler Impl.System.core0_rule_name_lift sched).
    Proof.
      induction sched; simpl; auto.
    Qed.

    Property equivalent_rules_core1_lift :
      forall sched,
      equivalent_rules
         (lift_rule Impl.System.Lift_core1 Impl.System.FnLift_id)
         (lift_scheduler Core1.rules sched)
         Impl.System.rules
         (lift_scheduler Impl.System.core1_rule_name_lift sched).
    Proof.
      induction sched; simpl; auto.
    Qed.

    Property equivalent_rules_sm_lift :
      forall (sched: scheduler),
      equivalent_rules
         (lift_rule Impl.System.Lift_sm Impl.System.FnLift_id)
         (lift_scheduler Impl.System.SM.rules sched)
         Impl.System.rules
         (lift_scheduler Impl.System.sm_rule_name_lift sched).
    Proof.
      induction sched; simpl; auto.
    Qed.

    Property equivalent_rules_mem_lift :
      forall (sched: scheduler),
      equivalent_rules
         (lift_rule Impl.System.Lift_mem Impl.System.FnLift_id)
         (lift_scheduler Memory.rules sched)
         Impl.System.rules
         (lift_scheduler Impl.System.mem_rule_name_lift sched).
    Proof.
      induction sched; simpl; auto.
    Qed.

  End TODO_WF_Properties.

  Import Common.

  (* ================= TMP ====================== *)
  Definition impl_log_t : Type := Impl.log_t.
  Definition spec0_log_t : Type := Spec.Machine0.log_t.
  Definition spec1_log_t : Type := Spec.Machine1.log_t.

  (* ================= END_TMP ====================== *)

  Section ImplRegisterMap.
    Definition impl_sm_clk : Impl.System.reg_t := Impl.System.SM_private (SM_Common.clk).
    Definition impl_purge_core0 : Impl.System.reg_t := Impl.System.purge_core0.
    Definition impl_purge_core1: Impl.System.reg_t := Impl.System.purge_core1.
    Definition impl_purge_mem0 : Impl.System.reg_t := Impl.System.purge_mem0.
    Definition impl_purge_mem1 : Impl.System.reg_t := Impl.System.purge_mem1.
  End ImplRegisterMap.

  (* TODO: fix this/put into a module *)
  Section Derived_Core0.
    Definition core0_state_t := @Core_Common.state Core0.private_params.

    Definition core0_initial_spec_state : Core_Common.spec_state_t :=
      @Core_Common.initial_spec_state Params0.core_id
                                      Params0.initial_pc
                                      Core0.private_params.

    Definition core0_do_step_input__koika :=
      @Core_Common.do_step_input__koika Core0.private_params
                                      External.ext
                                      Core0.rule_name_t
                                      Core0.rules
                                      Core0.schedule.

    Definition core0_do_step__koika :=
      @Core_Common.do_step__koika Core0.private_params
                                      External.ext
                                      Core0.rule_name_t
                                      Core0.rules
                                      Core0.schedule.

    Definition core0_do_steps__koika :=
      @Core_Common.do_steps__koika Params0.core_id
                                 Params0.initial_pc
                                 Core0.private_params
                                 External.ext
                                 Core0.rule_name_t
                                 Core0.rules
                                 Core0.schedule.


    Definition core0_spec_state_t : Type := @Core_Common.spec_state_t Core0.private_params.

    Definition core0_do_step_trans_input__spec :=
      @Core_Common.do_step_trans_input__spec Core0.private_params
                                           External.ext
                                           Core0.rule_name_t
                                           Core0.rules
                                           Core0.schedule.
    Definition core0_do_step__spec :=
      @Core_Common.do_step__spec Params0.core_id
                               Params0.initial_pc
                               Core0.private_params
                               External.ext
                               Core0.rule_name_t
                               Core0.rules
                               Core0.schedule.

    Definition core0_do_steps__spec :=
      @Core_Common.do_steps__spec Params0.core_id
                                Params0.initial_pc
                                Core0.private_params
                                External.ext
                                Core0.rule_name_t
                                Core0.rules
                                Core0.schedule.




  End Derived_Core0.

  Section Derived_Core1.

    Definition core1_state_t := @Core_Common.state Core1.private_params.

    Definition core1_initial_spec_state : Core_Common.spec_state_t :=
      @Core_Common.initial_spec_state Params1.core_id
                                      Params1.initial_pc
                                      Core1.private_params.

    Definition core1_do_step_input__koika :=
      @Core_Common.do_step_input__koika Core1.private_params
                                      External.ext
                                      Core1.rule_name_t
                                      Core1.rules
                                      Core1.schedule.

    Definition core1_do_step__koika :=
      @Core_Common.do_step__koika Core1.private_params
                                      External.ext
                                      Core1.rule_name_t
                                      Core1.rules
                                      Core1.schedule.

    Definition core1_do_steps__koika :=
      @Core_Common.do_steps__koika Params1.core_id
                                 Params1.initial_pc
                                 Core1.private_params
                                 External.ext
                                 Core1.rule_name_t
                                 Core1.rules
                                 Core1.schedule.


    Definition core1_spec_state_t : Type := @Core_Common.spec_state_t Core1.private_params.

    Definition core1_do_step_trans_input__spec :=
      @Core_Common.do_step_trans_input__spec Core1.private_params
                                           External.ext
                                           Core1.rule_name_t
                                           Core1.rules
                                           Core1.schedule.

    Definition core1_do_step__spec :=
      @Core_Common.do_step__spec Params1.core_id
                               Params1.initial_pc
                               Core1.private_params
                               External.ext
                               Core1.rule_name_t
                               Core1.rules
                               Core1.schedule.

    Definition core1_do_steps__spec :=
      @Core_Common.do_steps__spec Params1.core_id
                                Params1.initial_pc
                                Core1.private_params
                                External.ext
                                Core1.rule_name_t
                                Core1.rules
                                Core1.schedule.

  End Derived_Core1.

  Section Derived_Mem.
    Check Mem_Common.initial_spec_state.

    Definition mem_initial_spec_state : Mem_Common.dram_t -> Mem_Common.spec_state_t :=
      @Mem_Common.initial_spec_state Memory.private_params
                                     EnclaveParams.params
                                     Memory.private_external_state_t
                                     Memory.initial_private_external_state.

    Definition mem_do_step_input__impl :=
      @Mem_Common.do_step_input__impl Memory.private_params
                                    External.ext
                                    Memory.rule_name_t
                                    Memory.rules
                                    Memory.schedule
                                    Memory.private_external_state_t
                                    Memory.external_update_function.

    Definition mem_do_step__impl :=
      @Mem_Common.do_step__impl Memory.private_params
                                    External.ext
                                    Memory.rule_name_t
                                    Memory.rules
                                    Memory.schedule
                                    Memory.private_external_state_t
                                    Memory.external_update_function.

    Definition mem_do_steps__impl :=
      @Mem_Common.do_steps__impl Memory.private_params
                               External.ext
                               Memory.rule_name_t
                               Memory.rules
                               Memory.schedule
                               Memory.private_external_state_t
                               Memory.initial_private_external_state
                               Memory.external_update_function.


    Definition mem_spec_state_t : Type :=
      @Mem_Common.spec_state_t Memory.private_params Memory.private_external_state_t.

    Definition mem_do_step_trans_input__spec :=
      @Mem_Common.do_step_trans_input__spec Memory.private_params
                                          External.ext
                                          Memory.rule_name_t
                                          Memory.rules
                                          Memory.schedule
                                          Memory.private_external_state_t
                                          Memory.external_update_function.
    Definition mem_do_step__spec :=
      @Mem_Common.do_step__spec Memory.private_params
                              External.ext
                              EnclaveParams.params
                              Memory.rule_name_t
                              Memory.rules
                              Memory.schedule
                              Memory.private_external_state_t
                              Memory.initial_private_external_state
                              Memory.external_update_function.

    Definition mem_do_steps__spec :=
      @Mem_Common.do_steps__spec Memory.private_params
                               External.ext
                               EnclaveParams.params
                               Memory.rule_name_t
                               Memory.rules
                               Memory.schedule
                               Memory.private_external_state_t
                               Memory.initial_private_external_state
                               Memory.external_update_function.

  End Derived_Mem.

  Ltac unfold_core0_steps :=
    consider core0_do_steps__koika;
    consider core0_do_step_input__koika;
    consider core0_do_steps__spec;
    consider core0_do_step_trans_input__spec.

  Ltac unfold_core1_steps :=
    consider core1_do_steps__koika;
    consider core1_do_step_input__koika;
    consider core1_do_steps__spec;
    consider core1_do_step_trans_input__spec.

  Ltac unfold_sm_steps :=
    consider Impl.System.SM.do_steps__impl;
    consider Impl.System.SM.do_step_input__impl;
    consider Impl.System.SM.do_steps__spec.

  Ltac unfold_mem_steps :=
    consider mem_do_steps__impl;
    consider mem_do_step_input__impl;
    consider mem_do_steps__spec.

  Ltac unfold_all_steps :=
    unfold_core0_steps;
    unfold_core1_steps;
    unfold_sm_steps;
    unfold_mem_steps.


  Section ImplProjs.
    Definition get_impl_core0 : Impl.koika_state_t -> core0_state_t :=
      fun impl_st => proj_env Impl.System.Lift_core0 impl_st.
    Definition get_impl_core1 : Impl.koika_state_t -> core1_state_t :=
      fun impl_st => proj_env Impl.System.Lift_core1 impl_st.
    Definition get_impl_sm : Impl.koika_state_t -> SM_Common.state :=
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
    Definition get_spec0_core0 : Spec.Machine0.koika_state_t -> core0_state_t :=
      fun spec_st => proj_env Spec.Machine0.System.Lift_core0 spec_st.
    Definition get_spec1_core1 : Spec.Machine1.koika_state_t -> core1_state_t :=
      fun spec_st => proj_env Spec.Machine1.System.Lift_core1 spec_st.
    Definition get_spec0_sm : Spec.Machine0.koika_state_t -> SM_Common.state :=
      fun spec_st => proj_env Spec.Machine0.System.Lift_sm spec_st.
    Definition get_spec1_sm : Spec.Machine1.koika_state_t -> SM_Common.state :=
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
      { state_core0 : core0_state_t
      ; state_core1 : core1_state_t
      ; state_sm : SM_Common.state
      ; state_mem : Memory.state
      }.

    Record tau :=
      { output_core0 : Log Core0.R ContextEnv
      ; output_core1 : Log Core1.R ContextEnv
      ; output_sm : Log SM_Common.R ContextEnv
      ; output_mem : Log Memory.R ContextEnv (* * Memory.external_state_t *)
      }.

    Definition trace := list tau.

    Section TODO_MOVE.

      Definition TODO_ghost_state_conversion (st: SM_Common.ghost_output) : sm_ghost_output_t :=
        {| ghost_output_config0 := SM_Common.ghost_output_config0 st;
           ghost_output_config1 := SM_Common.ghost_output_config1 st
        |}.

    End TODO_MOVE.

    Definition initial_state (initial_dram: dram_t) : state :=
      {| state_core0 := ContextEnv.(create) Core0.r;
         state_core1 := ContextEnv.(create) Core1.r;
         state_sm := ContextEnv.(create) Impl.System.SM.r;
         state_mem := (ContextEnv.(create) Memory.r, Memory.initial_external_state initial_dram)
      |}.

    (* TODO: stop duplicating *)
    Section ModularStep.

      Record mod_step_io :=
        { step_io_core0 : Core_Common.step_io;
          step_io_core1 : Core_Common.step_io;
          step_io_sm : SM_Common.step_io;
          step_io_mem : Mem_Common.step_io
        }.

      Definition do_core0 (st: core0_state_t) (input_log: Log Impl.System.R ContextEnv)
                          : Log Core_Common.R_public ContextEnv * Log Core0.R ContextEnv *
                            Log Impl.System.R ContextEnv * Log Impl.System.R ContextEnv *
                            (Log Impl.System.R ContextEnv -> Core_Common.step_io) :=
        let core0_input := Core_Common.proj_log__pub (proj_log Impl.System.Lift_core0 input_log) in
        let '(core0_output__local, _) := core0_do_step_input__koika st core0_input in
        let core0_output__global := lift_log (REnv' := ContextEnv) Impl.System.Lift_core0 core0_output__local in
        let acc := log_app core0_output__global input_log in
        let mk_core0_step_io feedback_log :=
            {| Core_Common.step_input := core0_input;
               Core_Common.step_feedback := Core_Common.proj_log__pub (proj_log Impl.System.Lift_core0 feedback_log)
            |} in
        (core0_input, core0_output__local, core0_output__global, acc, mk_core0_step_io).

      Definition do_core1 (st: core1_state_t) (input_log: Log Impl.System.R ContextEnv)
                          : Log Core_Common.R_public ContextEnv * Log Core1.R ContextEnv *
                            Log Impl.System.R ContextEnv * Log Impl.System.R ContextEnv *
                            (Log Impl.System.R ContextEnv -> Core_Common.step_io) :=
        let core1_input := Core_Common.proj_log__pub (proj_log Impl.System.Lift_core1 input_log) in
        let '(core1_output__local, _) := core1_do_step_input__koika st core1_input in
        let core1_output__global := lift_log (REnv' := ContextEnv) Impl.System.Lift_core1 core1_output__local in
        let acc := log_app core1_output__global input_log in
        let mk_core1_step_io feedback_log :=
            {| Core_Common.step_input := core1_input;
               Core_Common.step_feedback := Core_Common.proj_log__pub (proj_log Impl.System.Lift_core1 feedback_log)
            |} in
        (core1_input, core1_output__local, core1_output__global, acc, mk_core1_step_io).

      Definition do_sm (st: SM_Common.state) (input_log: Log Impl.System.R ContextEnv)
                             : Log SM_Common.R_public ContextEnv * Log SM_Common.R ContextEnv *
                               Log Impl.System.R ContextEnv * Log Impl.System.R ContextEnv *
                               (Log Impl.System.R ContextEnv -> SM_Common.step_io) :=
        let sm_input := SM_Common.proj_log__pub (proj_log Impl.System.Lift_sm input_log) in
        let '(sm_output__local, _) := Impl.System.SM.do_step_input__impl st sm_input in
        let sm_output__global := lift_log (REnv' := ContextEnv) Impl.System.Lift_sm sm_output__local in
        let acc := log_app sm_output__global input_log in
        let mk_sm_step_io feedback_log :=
            {| SM_Common.step_input := sm_input;
               SM_Common.step_feedback := SM_Common.proj_log__pub (proj_log Impl.System.Lift_sm feedback_log)
            |} in
        (sm_input, sm_output__local, sm_output__global, acc, mk_sm_step_io).

      Definition do_mem (st: Memory.state) (input_log: Log Impl.System.R ContextEnv)
                        : Log Mem_Common.R_public ContextEnv * Log Memory.R ContextEnv *
                          Mem_Common.external_state_t * Log Impl.System.R ContextEnv * Log Impl.System.R ContextEnv *
                          (Log Impl.System.R ContextEnv -> Mem_Common.step_io) :=
        let mem_input := Mem_Common.proj_log__pub (proj_log (REnv := ContextEnv) Impl.System.Lift_mem input_log) in
        let '(mem_output__local, ext_st) := mem_do_step_input__impl st mem_input in
        let mem_output__global := lift_log (REnv := ContextEnv) Impl.System.Lift_mem mem_output__local in
        let acc_mem := log_app mem_output__global input_log in
        let mk_mem_step_io feedback_log :=
            {| Mem_Common.step_input := mem_input;
               Mem_Common.step_feedback := Mem_Common.proj_log__pub (proj_log Impl.System.Lift_mem feedback_log)
            |} in
        (mem_input, mem_output__local, ext_st, mem_output__global, acc_mem, mk_mem_step_io).

    End ModularStep.

    Definition compute_mod_outputs (st: state) : mod_step_io * tau :=
      (* Core0 *)
      let '(core0_input, core0_output__local, core0_output__global, acc__core0, mk_core0_step_io) :=
          do_core0 (state_core0 st) log_empty in
      (* Core1 *)
      let '(core1_input, core1_output__local, core1_output__global, acc__core1, mk_core1_step_io) :=
          do_core1 (state_core1 st) acc__core0 in
      (* SM *)
      let '(sm_input, sm_output__local, sm_output__global, acc_sm, mk_sm_step_io) :=
          do_sm (state_sm st) acc__core1 in
      (* Mem *)
      let '(mem_input, mem_output__local, ext_st, mem_output__global, acc_mem, mk_mem_step_io) :=
          do_mem (state_mem st) acc_sm in
      let outputs :=
        {| output_core0 := core0_output__local;
           output_core1 := core1_output__local;
           output_sm := sm_output__local ;
           output_mem := (mem_output__local) (*, ext_st) *)
        |} in
      (* Do feedback: reverse *)
      let mem_feedback__global := log_empty in
      let sm_feedback__global := log_app mem_feedback__global mem_output__global in
      let core1_feedback__global := log_app sm_feedback__global sm_output__global in
      let core0_feedback__global := log_app core1_feedback__global core1_output__global in

      ({| step_io_core0 := mk_core0_step_io core0_feedback__global;
          step_io_core1 := mk_core1_step_io core1_feedback__global;
          step_io_sm := mk_sm_step_io sm_feedback__global;
          step_io_mem := mk_mem_step_io mem_feedback__global
       |}, outputs).

    Definition compute_state (st: state) (step_io: mod_step_io) : state :=
      {| state_core0 := fst (core0_do_step__koika (state_core0 st) (step_io.(step_io_core0)));
         state_core1 := fst (core1_do_step__koika (state_core1 st) (step_io.(step_io_core1)));
         state_sm := fst (Impl.System.SM.do_step__impl (state_sm st) (step_io.(step_io_sm)));
         state_mem := fst (mem_do_step__impl (state_mem st) (step_io.(step_io_mem)))
      |}.

    (* TODO: Monad! *)
    (* TODO: fix Interfaces' do_step_input function *)
    (* TODO: Modularize *)

    (* Helper function *)
    Definition do_step_with_metadata (st: state) : state * tau * mod_step_io :=
      let (step_io, outputs) := compute_mod_outputs st in
      let st' := compute_state st step_io in
      ((st', outputs), step_io).

    Definition do_step (st: state) : state * tau :=
      fst (do_step_with_metadata st).

    Fixpoint step_n_with_metadata (initial_dram: dram_t) (n: nat) : state * trace * list mod_step_io :=
      match n with
      | 0 => (initial_state initial_dram, [], [])
      | S n' =>
          let '(st, evs, ios) := step_n_with_metadata initial_dram n' in
          let '(st', ev, io) := do_step_with_metadata st in
          (st', evs ++ [ev], ios ++ [io])
      end.

    Definition step_n (initial_dram: dram_t) (n: nat) : state * trace :=
      Framework.step_n (initial_state initial_dram) do_step n.

    Section HelperLemmas.

      Definition outputs_to_impl_log (ev: tau) : impl_log_t :=
        let core0_log := lift_log Impl.System.Lift_core0 ev.(output_core0) in
        let core1_log := lift_log Impl.System.Lift_core1 ev.(output_core1) in
        let sm_log := lift_log Impl.System.Lift_sm ev.(output_sm) in
        let mem_log := lift_log Impl.System.Lift_mem ev.(output_mem) in
        (mem_log ++ sm_log ++ core1_log ++ core0_log)%log.

      Definition core0_function_of_decoupled_io__state (st: core0_state_t) (ios: list Core_Common.step_io) : Prop :=
        st = fst (core0_do_steps__koika ios).

      Definition core1_function_of_decoupled_io__state (st: core1_state_t) (ios: list Core_Common.step_io) : Prop :=
        st = fst (core1_do_steps__koika ios).

      Definition sm_function_of_decoupled_io__state (st: SM_Common.state) (ios: list SM_Common.step_io) : Prop :=
        st = fst (Impl.System.SM.do_steps__impl ios).

      Definition mem_function_of_decoupled_io__state
                 (initial_dram: dram_t) (st: Memory.state) (ios: list Mem_Common.step_io) : Prop :=
        st = fst (mem_do_steps__impl initial_dram ios).

      Definition state_function_of_decoupled_ios (initial_dram: dram_t) (st: state) (step_ios: list mod_step_io) :=
        core0_function_of_decoupled_io__state st.(state_core0) (map step_io_core0 step_ios) /\
        core1_function_of_decoupled_io__state st.(state_core1) (map step_io_core1 step_ios) /\
        sm_function_of_decoupled_io__state st.(state_sm) (map step_io_sm step_ios) /\
        mem_function_of_decoupled_io__state initial_dram st.(state_mem) (map step_io_mem step_ios).

      Ltac unfold_decoupled_ios__state :=
        consider @core0_function_of_decoupled_io__state;
        consider @core1_function_of_decoupled_io__state;
        consider @sm_function_of_decoupled_io__state;
        consider @mem_function_of_decoupled_io__state.


      Lemma step_state_function_of_decoupled_ios :
        forall initial_dram st ios st' t io,
        state_function_of_decoupled_ios initial_dram st ios ->
        do_step_with_metadata st = (st', t, io) ->
        state_function_of_decoupled_ios initial_dram st' (ios ++ [io]).
      Proof.
        intros *; intros Hdec Hstep.
        consider state_function_of_decoupled_ios; unfold_decoupled_ios__state; propositional.
        repeat rewrite map_app.
        consider do_step_with_metadata.
        consider compute_mod_outputs.
        consider compute_state.
        repeat (destruct_matches_in_hyp Hstep; simplify_tuples; subst).
        intuition; simpl.
        - unfold_core0_steps.
          rewrite Core_Common.do_steps__koika_app__state.
          simpl; rewrite_solve.
        - unfold_core1_steps.
          rewrite Core_Common.do_steps__koika_app__state.
          simpl; rewrite_solve.
        - unfold_sm_steps.
          rewrite SM_Common.do_steps__impl_app__state.
          simpl; rewrite_solve.
        - unfold_mem_steps.
          rewrite Mem_Common.do_steps__impl_app__state.
          simpl; rewrite_solve.
      Qed.

      Theorem step_rel_decoupled_step__state :
        forall (initial_dram: dram_t) (n: nat)
          (st: state) (tr: trace) (step_ios : list mod_step_io),
          step_n_with_metadata initial_dram n = (st, tr, step_ios) ->
          state_function_of_decoupled_ios initial_dram st step_ios.
      Proof.
        induction n.
        - simpl; intuition; simplify_tuples; subst; auto;
            consider state_function_of_decoupled_ios; unfold_decoupled_ios__state; auto.
        - intros; simpl in *.
          repeat destruct_matches_in_hyp H; simplify_tuples; subst.
          specialize IHn with (1 := eq_refl); propositional.
          eapply step_state_function_of_decoupled_ios; eauto.
      Qed.

      Definition core0_function_of_decoupled_io__trace
                 (tr: list (Log Core0.R ContextEnv)) (ios: list Core_Common.step_io) : Prop :=
        tr = snd (core0_do_steps__koika ios).

      Definition core1_function_of_decoupled_io__trace
                 (tr: list (Log Core1.R ContextEnv)) (ios: list Core_Common.step_io) : Prop :=
        tr = snd (core1_do_steps__koika ios).

      Definition sm_function_of_decoupled_io__trace
                 (tr: list (Log SM_Common.R ContextEnv)) (ios: list SM_Common.step_io) : Prop :=
        tr = snd (Impl.System.SM.do_steps__impl ios).

      Definition mem_function_of_decoupled_io__trace
                 (initial_dram: dram_t) (tr: list (Log Memory.R ContextEnv)) (ios: list Mem_Common.step_io) : Prop :=
        tr = snd (mem_do_steps__impl initial_dram ios).

      Definition trace_function_of_decoupled_ios (initial_dram: dram_t) (tr: trace) (step_ios: list mod_step_io) :=
        core0_function_of_decoupled_io__trace (map output_core0 tr) (map step_io_core0 step_ios) /\
        core1_function_of_decoupled_io__trace (map output_core1 tr) (map step_io_core1 step_ios) /\
        sm_function_of_decoupled_io__trace (map output_sm tr) (map step_io_sm step_ios) /\
        mem_function_of_decoupled_io__trace initial_dram (map output_mem tr) (map step_io_mem step_ios).

      Ltac unfold_decoupled_ios__trace :=
        consider @core0_function_of_decoupled_io__trace;
        consider @core1_function_of_decoupled_io__trace;
        consider @sm_function_of_decoupled_io__trace;
        consider @mem_function_of_decoupled_io__trace.

      Lemma step_trace_function_of_decoupled_ios :
        forall initial_dram st ios st' tr t io,
        state_function_of_decoupled_ios initial_dram st ios ->
        trace_function_of_decoupled_ios initial_dram tr ios ->
        do_step_with_metadata st = (st', t, io) ->
        trace_function_of_decoupled_ios initial_dram (tr ++ [t]) (ios ++ [io]).
      Proof.
        intros *; intros Hst Htr Hstep.
        consider trace_function_of_decoupled_ios; unfold_decoupled_ios__trace; propositional.
        repeat rewrite map_app.
        consider do_step_with_metadata.
        consider compute_mod_outputs.
        repeat (destruct_matches_in_hyp Hstep; simplify_tuples; subst).
        consider state_function_of_decoupled_ios; propositional; unfold_decoupled_ios__state.
        intuition; simpl.
        - rewrite Htr0.
          consider do_core0.
          unfold_core0_steps.
          destruct_matches_in_hyp Heqp.
          simplify_tuples; subst.
          rewrite<-Core_Common.do_steps__koika_app__trace.
          simpl Core_Common.step_input.
          rewrite<-Hst0.
          rewrite_solve.
        - rewrite Htr2.
          consider do_core1.
          unfold_core1_steps.
          destruct_matches_in_hyp Heqp0.
          simplify_tuples; subst.
          rewrite<-Core_Common.do_steps__koika_app__trace.
          simpl Core_Common.step_input.
          rewrite<-Hst2.
          rewrite_solve.
        - rewrite Htr1.
          consider do_sm.
          unfold_sm_steps.
          destruct_matches_in_hyp Heqp1.
          simplify_tuples; subst.
          rewrite Hst1 in Heqp3.
          rewrite<-SM_Common.do_steps__impl_app__trace.
          simpl SM_Common.step_input.
          rewrite_solve.
        - rewrite Htr4.
          consider do_mem.
          unfold_mem_steps.
          destruct_matches_in_hyp  Heqp2.
          simplify_tuples; subst.
          rewrite Hst4 in Heqp3.
          rewrite<-Mem_Common.do_steps__impl_app__trace.
          simpl Mem_Common.step_input.
          rewrite_solve.
      Qed.

      Theorem step_rel_decoupled_step__trace :
        forall (initial_dram: dram_t) (n: nat)
          (st: state) (tr: trace) (step_ios : list mod_step_io),
          step_n_with_metadata initial_dram n = (st, tr, step_ios) ->
          trace_function_of_decoupled_ios initial_dram tr step_ios.
      Proof.
        induction n.
        - simpl; intuition; simplify_tuples; subst; auto;
            consider trace_function_of_decoupled_ios; unfold_decoupled_ios__trace; auto.
        - intros; simpl in *.
          repeat destruct_matches_in_hyp H; simplify_tuples; subst.
          specialize IHn with (1 := eq_refl); propositional.
          eapply step_trace_function_of_decoupled_ios; eauto.
          eapply step_rel_decoupled_step__state; eauto.
      Qed.

      Theorem step_n_extract_ios :
        forall (initial_dram: dram_t) (n: nat)
          (st: state) (tr: trace),
          step_n initial_dram n = (st, tr) ->
          exists step_ios, step_n_with_metadata initial_dram n = (st, tr, step_ios).
      Proof.
        induction n.
        - simpl; intros; simplify_tuples; subst.
          exists []; auto.
        - simpl; intros; destruct_all_matches; simplify_tuples; subst.
          exists (l ++ [m]).
          specialize IHn with (1 := eq_refl); propositional; simplify_tuples; subst.
          consider do_step.
          rewrite Heqp1 in *. simpl in *. simplify_tuples; subst.
          auto.
      Qed.

      Ltac solve_extract_steps_from_metadata :=
        let HStep := fresh in
        intros *; intro HStep; unfold_all_steps;
          specialize step_rel_decoupled_step__state with (1 := HStep); intro Hstate;
          specialize step_rel_decoupled_step__trace with (1 := HStep); intro Htrace;
          consider state_function_of_decoupled_ios;
          consider trace_function_of_decoupled_ios;
          propositional;
          unfold_decoupled_ios__state;
          unfold_decoupled_ios__trace;
          unfold_all_steps;
          rewrite_in_goal; solve'.

      Corollary extract_core0_steps_from_metadata :
        forall initial_dram n st tr io,
        step_n_with_metadata initial_dram n = (st, tr, io) ->
        core0_do_steps__koika (map step_io_core0 io) = (state_core0 st, map output_core0 tr).
      Proof.
        solve_extract_steps_from_metadata.
      Qed.

      Corollary extract_core1_steps_from_metadata :
        forall initial_dram n st tr io,
        step_n_with_metadata initial_dram n = (st, tr, io) ->
        core1_do_steps__koika (map step_io_core1 io) = (state_core1 st, map output_core1 tr).
      Proof.
        solve_extract_steps_from_metadata.
      Qed.

      Corollary extract_sm_steps_from_metadata :
        forall initial_dram n st tr io,
        step_n_with_metadata initial_dram n = (st, tr, io) ->
        Impl.System.SM.do_steps__impl (map step_io_sm io) = (state_sm st, map output_sm tr).
      Proof.
        solve_extract_steps_from_metadata.
      Qed.

      Corollary extract_mem_steps_from_metadata :
        forall initial_dram n st tr io,
        step_n_with_metadata initial_dram n = (st, tr, io) ->
        mem_do_steps__impl initial_dram (map step_io_mem io) = (state_mem st, map output_mem tr).
      Proof.
        solve_extract_steps_from_metadata.
      Qed.

    End HelperLemmas.

  End ModImpl.

  Module ModSpec.

    Record state :=
      { state_core0 : core0_spec_state_t
      ; state_core1 : core1_spec_state_t
      ; state_sm : SM_Common.spec_state_t
      ; state_mem : mem_spec_state_t
      }.

    Record tau :=
      { output_core0 : Log Core0.R ContextEnv
      ; output_core1 : Log Core1.R ContextEnv
      ; output_sm : SM_Common.spec_output_t
      ; output_mem : Log Memory.R ContextEnv * Log Memory.R ContextEnv (* * Memory.external_state_t *)
      }.

    Definition trace := list tau.

    Definition initial_state (initial_dram: dram_t): state :=
      {| state_core0 := core0_initial_spec_state;
         state_core1 := core1_initial_spec_state;
         state_sm := @SM_Common.initial_spec_state Params0.initial_pc Params1.initial_pc
                                                   EnclaveParams.params External.ext;
         state_mem := mem_initial_spec_state initial_dram
      |}.

    Section TODO_MOVE.

      Definition TODO_ghost_state_conversion (st: SM_Common.ghost_output) : sm_ghost_output_t :=
        {| ghost_output_config0 := SM_Common.ghost_output_config0 st;
           ghost_output_config1 := SM_Common.ghost_output_config1 st
        |}.

      Definition combine_spec_public_output : SM_Common.spec_output_t ->
                                              Log SM_Common.R ContextEnv * sm_ghost_output_t :=
        fun '(output0, output1) =>
          let log := ContextEnv.(create)
              (fun reg => match reg with
                       | SM_Common.public reg' =>
                           match SM_Common.public_reg_to_core_id reg' with
                           | CoreId0 =>
                               ContextEnv.(getenv) (fst output0) (SM_Common.public reg')
                           | CoreId1 =>
                               ContextEnv.(getenv) (fst output1) (SM_Common.public reg')
                           end
                       | SM_Common.private _ => []
                       end) in
        (log, {| ghost_output_config0 := snd output0;
                 ghost_output_config1 := snd output1 |}).

      Definition combine_mem_public_output
        : Log Memory.R ContextEnv * Log Memory.R ContextEnv -> Log Memory.R ContextEnv :=
        fun '(log0, log1) =>
          ContextEnv.(create)
            (fun reg => match reg with
                     | Mem_Common.public reg' =>
                         match Mem_Common.public_reg_to_taint reg' with
                         | CoreId0 => ContextEnv.(getenv) log0 (Mem_Common.public reg')
                         | CoreId1 => ContextEnv.(getenv) log1 (Mem_Common.public reg')
                         end
                     | Mem_Common.private _ => []
                     end).

      Record mod_step_io :=
        { step_io_core0 : Core_Common.step_io;
          step_io_core1 : Core_Common.step_io;
          step_io_sm : SM_Common.step_io * sm_ghost_output_t;
          step_io_mem : Mem_Common.ghost_io
        }.

    End TODO_MOVE.

    (* TODO: stop duplicating. *)
    Section ModularStep.

      (* TODO: For global, we only care about public interface *)
      Definition do_core0 (st: core0_spec_state_t) (input_log: Log Impl.System.R ContextEnv)
                          : (* projected input log *)     Log Core_Common.R_public ContextEnv *
                            (* Core0 output log *)        Log Core0.R ContextEnv *
                            (* Core0 global log *)        Log Impl.System.R ContextEnv *
                            (* Accumulated log *)         Log Impl.System.R ContextEnv *
                            (Log Core_Common.R_public ContextEnv -> Core_Common.step_io) :=
        let core0_input := Core_Common.proj_log__pub (proj_log Impl.System.Lift_core0 input_log) in
        let '(core0_output__local, _) := core0_do_step_trans_input__spec st core0_input in
        let core0_output__global := lift_log (REnv' := ContextEnv) Impl.System.Lift_core0 core0_output__local in
        let acc := log_app core0_output__global input_log in
        let mk_core0_step_io feedback_log :=
            {| Core_Common.step_input := core0_input;
               Core_Common.step_feedback := feedback_log
            |} in
        (core0_input, core0_output__local, core0_output__global, acc, mk_core0_step_io).

      Definition do_core1 (st: core1_spec_state_t) (input_log: Log Impl.System.R ContextEnv)
                          : Log Core_Common.R_public ContextEnv * Log Core1.R ContextEnv *
                            Log Impl.System.R ContextEnv * Log Impl.System.R ContextEnv *
                            (Log Core_Common.R_public ContextEnv -> Core_Common.step_io) :=
        let core1_input := Core_Common.proj_log__pub (proj_log Impl.System.Lift_core1 input_log) in
        let '(core1_output__local, _) := core1_do_step_trans_input__spec st core1_input in
        let core1_output__global := lift_log (REnv' := ContextEnv) Impl.System.Lift_core1 core1_output__local in
        let acc := log_app core1_output__global input_log in
        let mk_core1_step_io feedback_log :=
            {| Core_Common.step_input := core1_input;
               Core_Common.step_feedback := feedback_log
            |} in
        (core1_input, core1_output__local, core1_output__global, acc, mk_core1_step_io).

      Definition do_sm (st: SM_Common.spec_state_t) (input_log: Log Impl.System.R ContextEnv)
                       : Log SM_Common.R_public ContextEnv * SM_Common.spec_output_t *
                         Log Impl.System.R ContextEnv * Log Impl.System.R ContextEnv *
                         (Log SM_Common.R_public ContextEnv -> SM_Common.step_io) *
                         sm_ghost_output_t :=
        let sm_input := SM_Common.proj_log__pub (proj_log Impl.System.Lift_sm input_log) in
        let sm_output__raw := Impl.System.SM.do_step_input__spec st sm_input in
        let '(sm_output__local, sm_ghost) := combine_spec_public_output sm_output__raw in
        let sm_output__global := lift_log (REnv' := ContextEnv) Impl.System.Lift_sm sm_output__local in
        let acc := log_app sm_output__global input_log in
        let mk_sm_step_io feedback_log :=
            {| SM_Common.step_input := sm_input;
               SM_Common.step_feedback := feedback_log
            |} in
        (sm_input, sm_output__raw, sm_output__global, acc, mk_sm_step_io, sm_ghost).

      Definition do_mem (st: mem_spec_state_t)
                        (input_log: Log Impl.System.R ContextEnv)
                        (ghost: sm_ghost_output_t)
                        : Log Mem_Common.R_public ContextEnv *
                          (Log Mem_Common.R ContextEnv * Log Mem_Common.R ContextEnv) *
                          Log Impl.System.R ContextEnv * Log Impl.System.R ContextEnv *
                          (Log Mem_Common.R_public ContextEnv -> Mem_Common.ghost_io) :=
        let mem_input := Mem_Common.proj_log__pub (proj_log (REnv := ContextEnv) Impl.System.Lift_mem input_log) in
        let mem_output__raw := mem_do_step_trans_input__spec
                               st (mem_input, (ghost_output_config0 ghost, ghost_output_config1 ghost)) in
        let mem_output__local := combine_mem_public_output mem_output__raw in
        let mem_output__global := lift_log (REnv := ContextEnv) Impl.System.Lift_mem mem_output__local in
        let acc_mem := log_app mem_output__global input_log in
        let mk_mem_step_io feedback_log :=
            {| Mem_Common.step_input := mem_input;
               Mem_Common.step_feedback := feedback_log
            |} in
        let mk_mem_ghost_io feedback_log :=
            {| Mem_Common.ghost_step := mk_mem_step_io feedback_log;
               Mem_Common.ghost_input_config0 := ghost_output_config0 ghost;
               Mem_Common.ghost_input_config1 := ghost_output_config1 ghost
            |} in
        (* TODO: should we output external state here too? *)
        (mem_input, mem_output__raw, mem_output__global, acc_mem, mk_mem_ghost_io).

    End ModularStep.

    (* TODO: this is kind of awkward *)
    (* Global => public only? *)
    Definition compute_mod_outputs (st: state) : mod_step_io * tau :=
      (* Core0 *)
      let '(core0_input, core0_output__local, core0_output__global, acc__core0, mk_core0_step_io) :=
          do_core0 (state_core0 st) log_empty in
      (* Core1 *)
      let '(core1_input, core1_output__local, core1_output__global, acc__core1, mk_core1_step_io) :=
          do_core1 (state_core1 st) acc__core0 in
      (* SM *)
      let '(sm_input, sm_output__raw, sm_output__global, acc_sm, mk_sm_step_io, sm_ghost) :=
          do_sm (state_sm st) acc__core1 in
      (* Mem *)
      let '(mem_input, mem_output__raw, (* ext_st, *) mem_output__global, acc_mem, mk_mem_ghost_io) :=
          do_mem (state_mem st) acc_sm sm_ghost in
      (* Do feedback: reverse *)
      let mem_feedback__global := log_empty in
      let sm_feedback__global := log_app mem_feedback__global mem_output__global in
      let core1_feedback__global := log_app sm_feedback__global sm_output__global in
      let core0_feedback__global := log_app core1_feedback__global core1_output__global in

      let outputs :=
        {| output_core0 := core0_output__local;
           output_core1 := core1_output__local;
           output_sm := sm_output__raw ;
           output_mem := mem_output__raw (*, ext_st) *)
        |} in

      ({| step_io_core0 := mk_core0_step_io
                             (Core_Common.proj_log__pub (proj_log Impl.System.Lift_core0 core0_feedback__global));
          step_io_core1 := mk_core1_step_io
                             (Core_Common.proj_log__pub (proj_log Impl.System.Lift_core1 core1_feedback__global));
          step_io_sm := (mk_sm_step_io (SM_Common.proj_log__pub (proj_log Impl.System.Lift_sm sm_feedback__global)),
                         sm_ghost);
          step_io_mem := mk_mem_ghost_io (Mem_Common.proj_log__pub (proj_log Impl.System.Lift_mem mem_feedback__global))
       |}, outputs).

    Definition compute_state (st: state) (step_io: mod_step_io) : state :=
      {| state_core0 := fst (fst (core0_do_step__spec (state_core0 st) (step_io.(step_io_core0))));
         state_core1 := fst (fst (core1_do_step__spec (state_core1 st) (step_io.(step_io_core1))));
         state_sm := fst (fst (Impl.System.SM.do_step__spec (state_sm st) (fst (step_io.(step_io_sm)))));
         state_mem := fst (fst (mem_do_step__spec (state_mem st) (step_io.(step_io_mem))))
      |}.

    Definition do_step_with_metadata (st: state) : state * tau * mod_step_io :=
      let (step_io, outputs) := compute_mod_outputs st in
      let st' := compute_state st step_io in
      ((st', outputs), step_io).

    Definition do_step (st: state) : state * tau :=
      fst (do_step_with_metadata st).

    Fixpoint step_n_with_metadata (initial_dram: dram_t) (n: nat) : state * trace * list mod_step_io :=
      match n with
      | 0 => (initial_state initial_dram, [], [])
      | S n' =>
          let '(st, evs, ios) := step_n_with_metadata initial_dram n' in
          let '(st', ev, io) := do_step_with_metadata st in
          (st', evs ++ [ev], ios ++ [io])
      end.

    Definition step_n (initial_dram: dram_t) (n: nat) : state * trace :=
      Framework.step_n (initial_state initial_dram) do_step n.

    Section HelperLemmas.
      Definition outputs_to_spec_log (ev: tau) : (spec0_log_t * spec1_log_t) :=
        let core0_log := lift_log (REnv' := ContextEnv) Spec.Machine0.System.Lift_core0 ev.(output_core0) in
        let core1_log := lift_log (REnv' := ContextEnv) Spec.Machine1.System.Lift_core1 ev.(output_core1) in
        let sm0_log := lift_log (REnv' := ContextEnv) Spec.Machine0.System.Lift_sm (fst (fst ev.(output_sm))) in
        let sm1_log := lift_log (REnv' := ContextEnv) Spec.Machine1.System.Lift_sm (fst (snd ev.(output_sm))) in
        let mem0_log := lift_log (REnv' := ContextEnv) Spec.Machine0.System.Lift_mem (fst ev.(output_mem)) in
        let mem1_log := lift_log (REnv' := ContextEnv) Spec.Machine1.System.Lift_mem (snd ev.(output_mem)) in
        (* Define machine logs *)
        let machine0_log := (mem0_log ++ sm0_log ++ core0_log)%log in
        let machine1_log := (mem1_log ++ sm1_log ++ core1_log)%log in
        (machine0_log, machine1_log).

      Definition core0_function_of_decoupled_io__state (st: core0_spec_state_t) (ios: list Core_Common.step_io) : Prop :=
        st = fst (fst (core0_do_steps__spec ios)).

      Definition core1_function_of_decoupled_io__state (st: core1_spec_state_t) (ios: list Core_Common.step_io) : Prop :=
        st = fst (fst (core1_do_steps__spec ios)).

      Definition sm_function_of_decoupled_io__state (st: SM_Common.spec_state_t) (ios: list SM_Common.step_io) : Prop :=
        st = fst (fst (Impl.System.SM.do_steps__spec ios)).

      Definition mem_function_of_decoupled_io__state
                 (initial_dram: dram_t) (st: mem_spec_state_t) (ios: list Mem_Common.ghost_io) : Prop :=
        st = fst (fst (mem_do_steps__spec initial_dram ios)).

      Definition state_function_of_decoupled_ios
                 (initial_dram: dram_t) (st: state) (step_ios: list mod_step_io) : Prop :=
        core0_function_of_decoupled_io__state st.(state_core0) (map step_io_core0 step_ios) /\
        core1_function_of_decoupled_io__state st.(state_core1) (map step_io_core1 step_ios) /\
        sm_function_of_decoupled_io__state st.(state_sm) ((map fst (map step_io_sm step_ios))) /\
        mem_function_of_decoupled_io__state initial_dram st.(state_mem) (map step_io_mem step_ios).

      Ltac unfold_decoupled_ios__state :=
        consider @core0_function_of_decoupled_io__state;
        consider @core1_function_of_decoupled_io__state;
        consider @sm_function_of_decoupled_io__state;
        consider @mem_function_of_decoupled_io__state.

      Lemma step_state_function_of_decoupled_ios :
        forall initial_dram st ios st' t io,
        state_function_of_decoupled_ios initial_dram st ios ->
        do_step_with_metadata st = (st', t, io) ->
        state_function_of_decoupled_ios initial_dram st' (ios ++ [io]).
      Proof.
        intros *; intros Hdec Hstep.
        consider state_function_of_decoupled_ios; unfold_decoupled_ios__state; propositional.
        repeat rewrite map_app.
        consider do_step_with_metadata.
        consider compute_mod_outputs.
        consider compute_state.
        repeat (destruct_matches_in_hyp Hstep; simplify_tuples; subst).
        intuition; simpl.
        - unfold_core0_steps.
          rewrite Core_Common.do_steps__spec_app__state.
          simpl; rewrite_solve.
        - unfold_core1_steps.
          rewrite Core_Common.do_steps__spec_app__state.
          simpl; rewrite_solve.
        - unfold_sm_steps.
          rewrite SM_Common.do_steps__spec_app__state.
          simpl; rewrite_solve.
        - unfold_mem_steps.
          rewrite Mem_Common.do_steps__spec_app__state.
          simpl; rewrite_solve.
      Qed.

      Theorem step_rel_decoupled_step__state :
        forall (initial_dram: dram_t) (n: nat)
          (st: state) (tr: trace) (step_ios : list mod_step_io),
          step_n_with_metadata initial_dram n = (st, tr, step_ios) ->
          state_function_of_decoupled_ios initial_dram st step_ios.
      Proof.
        induction n.
        - simpl; intuition; simplify_tuples; subst; auto;
            consider state_function_of_decoupled_ios; unfold_decoupled_ios__state; auto.
        - intros; simpl in *.
          repeat destruct_matches_in_hyp H; simplify_tuples; subst.
          specialize IHn with (1 := eq_refl); propositional.
          eapply step_state_function_of_decoupled_ios; eauto.
      Qed.

      Definition core0_function_of_decoupled_io__trace
                 (tr: list (Log Core0.R ContextEnv)) (ios: list Core_Common.step_io) : Prop :=
        tr = snd (fst (core0_do_steps__spec ios)).

      Definition core1_function_of_decoupled_io__trace
                 (tr: list (Log Core1.R ContextEnv)) (ios: list Core_Common.step_io) : Prop :=
        tr = snd (fst (core1_do_steps__spec ios)).

      Definition sm_function_of_decoupled_io__trace
                 (tr: list (SM_Common.spec_output_t)) (ios: list SM_Common.step_io) : Prop :=
        tr = snd (fst (Impl.System.SM.do_steps__spec ios)).

      Definition mem_function_of_decoupled_io__trace
                 (initial_dram: dram_t) (tr: list (Log Memory.R ContextEnv * Log Memory.R ContextEnv))
                 (ios: list Mem_Common.ghost_io) : Prop :=
        tr = snd (fst (mem_do_steps__spec initial_dram ios)).

      Definition trace_function_of_decoupled_ios
                 (initial_dram: dram_t) (tr: trace) (step_ios: list mod_step_io) : Prop :=
        core0_function_of_decoupled_io__trace (map output_core0 tr) (map step_io_core0 step_ios) /\
        core1_function_of_decoupled_io__trace (map output_core1 tr) (map step_io_core1 step_ios) /\
        sm_function_of_decoupled_io__trace (map output_sm tr) (map fst (map step_io_sm step_ios)) /\
        mem_function_of_decoupled_io__trace initial_dram (map output_mem tr) (map step_io_mem step_ios).

      Ltac unfold_decoupled_ios__trace :=
        consider @core0_function_of_decoupled_io__trace;
        consider @core1_function_of_decoupled_io__trace;
        consider @sm_function_of_decoupled_io__trace;
        consider @mem_function_of_decoupled_io__trace.

      Lemma step_trace_function_of_decoupled_ios :
        forall initial_dram st ios st' tr t io,
        state_function_of_decoupled_ios initial_dram st ios ->
        trace_function_of_decoupled_ios initial_dram tr ios ->
        do_step_with_metadata st = (st', t, io) ->
        trace_function_of_decoupled_ios initial_dram (tr ++ [t]) (ios ++ [io]).
      Proof.
        intros *; intros Hst Htr Hstep.
        consider trace_function_of_decoupled_ios; unfold_decoupled_ios__trace; propositional.
        repeat rewrite map_app.
        consider do_step_with_metadata.
        consider compute_mod_outputs.
        repeat (destruct_matches_in_hyp Hstep; simplify_tuples; subst).
        consider state_function_of_decoupled_ios; propositional; unfold_decoupled_ios__state.
        intuition; simpl.
        - rewrite Htr0.
          consider do_core0.
          unfold_core0_steps.
          destruct_matches_in_hyp Heqp.
          simplify_tuples; subst.
          repeat rewrite<-Core_Common.do_steps__spec_app__trace.
          simpl Core_Common.step_input.
          rewrite<-Hst0.
          rewrite_solve.
        - rewrite Htr2.
          consider do_core1.
          unfold_core1_steps.
          destruct_matches_in_hyp Heqp0.
          simplify_tuples; subst.
          rewrite<-Core_Common.do_steps__spec_app__trace.
          simpl Core_Common.step_input.
          rewrite<-Hst2.
          rewrite_solve.
        - rewrite Htr1.
          consider do_sm.
          unfold_sm_steps.
          destruct_matches_in_hyp Heqp1.
          simplify_tuples; subst.
          rewrite Hst1 in Heqp3.
          rewrite<-SM_Common.do_steps__spec_app__trace.
          simpl SM_Common.step_input.
          rewrite_solve.
        - rewrite Htr4.
          consider do_mem.
          unfold_mem_steps.
          simplify_tuples; subst.
          rewrite<-Mem_Common.do_steps__spec_app__trace.
          simpl Mem_Common.step_input.
          rewrite_solve.
      Qed.

      Theorem step_rel_decoupled_step__trace :
        forall (initial_dram: dram_t) (n: nat)
          (st: state) (tr: trace) (step_ios : list mod_step_io),
          step_n_with_metadata initial_dram n = (st, tr, step_ios) ->
          trace_function_of_decoupled_ios initial_dram tr step_ios.
      Proof.
        induction n.
        - simpl; intuition; simplify_tuples; subst; auto;
            consider trace_function_of_decoupled_ios; unfold_decoupled_ios__trace; auto.
        - intros; simpl in *.
          repeat destruct_matches_in_hyp H; simplify_tuples; subst.
          specialize IHn with (1 := eq_refl); propositional.
          eapply step_trace_function_of_decoupled_ios; eauto.
          eapply step_rel_decoupled_step__state; eauto.
      Qed.

      Theorem step_n_extract_ios :
        forall (initial_dram: dram_t) (n: nat)
          (st: state) (tr: trace),
          step_n initial_dram n = (st, tr) ->
          exists step_ios, step_n_with_metadata initial_dram n = (st, tr, step_ios).
      Proof.
        induction n.
        - simpl; intros; simplify_tuples; subst.
          exists []; auto.
        - simpl; intros; destruct_all_matches; simplify_tuples; subst.
          exists (l ++ [m]).
          specialize IHn with (1 := eq_refl); propositional; simplify_tuples; subst.
          consider do_step.
          rewrite Heqp1 in *. simpl in *. simplify_tuples; subst.
          auto.
      Qed.

      Ltac solve_extract_steps_from_metadata :=
        let Hmeta := fresh in
        let Hsteps := fresh in
        intros *; intro Hmeta;
        specialize step_rel_decoupled_step__state with (1 := Hmeta); intro Hstate;
        specialize step_rel_decoupled_step__trace with (1 := Hmeta); intro Htrace;
        match goal with
        | |- exists _, ?x = _ =>
            let props := fresh in
            destruct x as [[? ?] props] eqn:Hsteps; exists props
        end;
        consider state_function_of_decoupled_ios;
        consider trace_function_of_decoupled_ios;
        propositional;
        unfold_decoupled_ios__state;
        unfold_decoupled_ios__trace;
        rewrite Hsteps in *; simpl in *;
        subst; auto.

      Corollary extract_core0_steps_from_metadata :
        forall initial_dram n st tr io,
        step_n_with_metadata initial_dram n = (st, tr, io) ->
        exists props, core0_do_steps__spec (map step_io_core0 io) = (state_core0 st, map output_core0 tr, props).
      Proof.
        solve_extract_steps_from_metadata.
      Qed.

      Corollary extract_core1_steps_from_metadata :
        forall initial_dram n st tr io,
        step_n_with_metadata initial_dram n = (st, tr, io) ->
        exists props, core1_do_steps__spec (map step_io_core1 io) = (state_core1 st, map output_core1 tr, props).
      Proof.
        solve_extract_steps_from_metadata.
      Qed.

      Corollary extract_sm_steps_from_metadata :
        forall initial_dram n st tr io,
        step_n_with_metadata initial_dram n = (st, tr, io) ->
        exists props, Impl.System.SM.do_steps__spec (map fst (map step_io_sm io)) = (state_sm st, map output_sm tr, props).
      Proof.
        solve_extract_steps_from_metadata.
      Qed.

      Corollary extract_mem_steps_from_metadata :
        forall initial_dram n st tr io,
        step_n_with_metadata initial_dram n = (st, tr, io) ->
        exists props, mem_do_steps__spec initial_dram (map step_io_mem io) = (state_mem st, map output_mem tr, props).
      Proof.
        solve_extract_steps_from_metadata.
      Qed.

    End HelperLemmas.

    Section Invariant.
      Definition InvariantState (st: state) : Prop. Admitted.

      Lemma initial_invariant : forall dram, InvariantState (initial_state dram).
      Admitted.

      Definition core0_P_prop (P_prop: list props_t -> Prop) io :=
        P_prop (snd (core0_do_steps__spec io)).
      Definition core1_P_prop (P_prop: list props_t -> Prop) io :=
        P_prop (snd (core1_do_steps__spec io)).
      Definition sm_P_prop (P_prop: list props_t -> Prop) io :=
        P_prop (snd (Impl.System.SM.do_steps__spec io)).
      Definition mem_P_prop (P_prop: list props_t -> Prop) dram io :=
        P_prop (snd (mem_do_steps__spec dram io)).

      Definition valid_P_prop (P_prop: list props_t -> Prop) (initial_dram: dram_t) spec_io :=
        core0_P_prop P_prop (map step_io_core0 spec_io) /\
        core1_P_prop P_prop (map step_io_core1 spec_io) /\
        sm_P_prop P_prop (map fst (map step_io_sm spec_io)) /\
        mem_P_prop P_prop initial_dram (map step_io_mem spec_io).

      Definition valid_props initial_dram spec_io :=
        valid_P_prop valid_inputs initial_dram spec_io /\
        valid_P_prop valid_outputs initial_dram spec_io /\
        valid_P_prop valid_feedbacks initial_dram spec_io.

    Ltac unfold_props :=
      consider valid_props;
      consider valid_P_prop;
      consider core0_P_prop;
      consider core1_P_prop;
      consider sm_P_prop;
      consider mem_P_prop.

      Lemma valid_props_app :
        forall dram l1 l2,
        valid_props dram (l1 ++ l2) <->
        valid_props dram l1 /\ valid_props dram l2.
      Proof.
        split.
        - generalize l2. induction l1.
          + intuition; unfold_props; simpl;
            repeat split.
          + simpl; intros.
            split.
      Admitted.


      Theorem step_n_invariant :
        forall initial_dram n spec_st spec_tr spec_io,
        ModSpec.step_n_with_metadata initial_dram n = (spec_st, spec_tr, spec_io) ->
        InvariantState spec_st /\ valid_props initial_dram spec_io.
      Admitted.

    End Invariant.

  End ModSpec.

  Module Observations.
    Import Interfaces.Common.
    (* TODO: write this in a nicer way *)
    Definition generate_observations__modImpl (ev: ModImpl.tau) : tau :=
      fun core_id => Impl.do_observations (ModImpl.outputs_to_impl_log ev) core_id.

    (* TODO: might be easier to combine logs first *)
    Definition generate_observations__modSpec (ev: ModSpec.tau) : tau :=
      let '(log0, log1) := ModSpec.outputs_to_spec_log ev in
      fun core_id =>
        match core_id with
        | CoreId0 => Spec.Machine0.do_observations log0 CoreId0
        | CoreId1 => Spec.Machine1.do_observations log1 CoreId1
         end.

    (* TODO_MOVE *)
    Ltac unfold_impl_obs :=
      unfold Impl.observe_reqs, Impl.observe_resps, Impl.observe_enclaves,
             Impl.observe_imem_reqs, Impl.observe_imem_reqs0, Impl.observe_imem_reqs1,
             Impl.observe_dmem_reqs, Impl.observe_dmem_reqs0, Impl.observe_dmem_reqs1,
             Impl.observe_imem_resps, Impl.observe_imem_resps0, Impl.observe_imem_resps1,
             Impl.observe_dmem_resps, Impl.observe_dmem_resps0, Impl.observe_dmem_resps1,
             Impl.observe_enclave_reqs, Impl.observe_enclave_reqs0, Impl.observe_enclave_reqs1,
             Impl.observe_enclave_enters, Impl.observe_enclave_enter0, Impl.observe_enclave_enter1,
             Impl.observe_enclave_exits, Impl.observe_enclave_exit0, Impl.observe_enclave_exit1
             in *.
  End Observations.

  Module ModImplToModSpec.
    Import Observations.
    Import Interfaces.Common.

    Section Simulation.

      Inductive Sim_step_io (impl_io: ModImpl.mod_step_io) (spec_io: ModSpec.mod_step_io) :=
      | SimStepIo :
          forall (core0_sim: impl_io.(ModImpl.step_io_core0) = spec_io.(ModSpec.step_io_core0))
            (core1_sim: impl_io.(ModImpl.step_io_core1) = spec_io.(ModSpec.step_io_core1))
            (sm_sim: impl_io.(ModImpl.step_io_sm) = fst (spec_io.(ModSpec.step_io_sm)))
            (mem_sim: impl_io.(ModImpl.step_io_mem) = spec_io.(ModSpec.step_io_mem).(Mem_Common.ghost_step)),
          Sim_step_io impl_io spec_io.

      Ltac solve_forall_extract :=
        apply Forall2_ind; auto; simpl; intros;
        match goal with
        | H: Sim_step_io _ _ |- _ => destruct H
        end; rewrite_solve.

      Property forall_sim_step_extract_core0 :
        forall impl_ios spec_ios,
        Forall2 Sim_step_io impl_ios spec_ios ->
        map ModImpl.step_io_core0 impl_ios = map ModSpec.step_io_core0 spec_ios.
      Proof.
        solve_forall_extract.
      Qed.

      Property forall_sim_step_extract_core1 :
        forall impl_ios spec_ios,
        Forall2 Sim_step_io impl_ios spec_ios ->
        map ModImpl.step_io_core1 impl_ios = map ModSpec.step_io_core1 spec_ios.
      Proof.
        solve_forall_extract.
      Qed.

      Property forall_sim_step_extract_sm :
        forall impl_ios spec_ios,
        Forall2 Sim_step_io impl_ios spec_ios ->
        map ModImpl.step_io_sm impl_ios = map fst (map ModSpec.step_io_sm spec_ios).
      Proof.
        solve_forall_extract.
      Qed.

      Property forall_sim_step_extract_mem :
        forall impl_ios spec_ios,
        Forall2 Sim_step_io impl_ios spec_ios ->
        map ModImpl.step_io_mem impl_ios = map Mem_Common.ghost_step (map ModSpec.step_io_mem spec_ios).
      Proof.
        solve_forall_extract.
      Qed.

      (* TODO: fewer params after defining *)
      Definition core0_valid_input := @Core_Common.valid_input Core0.private_params.
      Definition core0_valid_output := @Core_Common.valid_output Params0.core_id Params0.initial_pc Core0.private_params External.ext Core0.rule_name_t Core0.rules Core0.schedule.
      Definition core0_valid_feedback := @Core_Common.valid_feedback Params0.core_id Params0.initial_pc Core0.private_params External.ext Core0.rule_name_t Core0.rules Core0.schedule.
      Definition core0_output_log_equivalent := @Core_Common.output_log_equivalent Params0.core_id Params0.initial_pc Core0.private_params External.ext Core0.rule_name_t Core0.rules Core0.schedule.
      Definition core1_valid_input := @Core_Common.valid_input Core1.private_params.
      Definition core1_valid_output := @Core_Common.valid_output Params1.core_id Params1.initial_pc Core1.private_params External.ext Core1.rule_name_t Core1.rules Core1.schedule.
      Definition core1_valid_feedback := @Core_Common.valid_feedback Params1.core_id Params1.initial_pc Core1.private_params External.ext Core1.rule_name_t Core1.rules Core1.schedule.

      Theorem step_n_ios_sim:
        forall initial_dram n impl_st impl_tr spec_st spec_tr impl_io spec_io,
        ModImpl.step_n_with_metadata initial_dram n = (impl_st, impl_tr, impl_io) ->
        ModSpec.step_n_with_metadata initial_dram n = (spec_st, spec_tr, spec_io) ->
        Forall2 Sim_step_io impl_io spec_io.
      Proof.
        induction n.
        - intros; simpl in *; simplify_tupless; auto.
        - intros *; intros HImpl HSpec.
          specialize ModSpec.step_n_invariant with (1 := HSpec); intros HSpecInv; propositional.
          simpl in HImpl, HSpec.
          destruct_all_matches; simplify_tupless.
          specialize IHn with (1 := eq_refl) (2 := eq_refl).
          rename s1 into impl_st0; rename s into spec_st0.
          rename m0 into impl_io; rename m into spec_io.

          apply Forall2_app; auto.
          constructor; auto.
          rename t0 into spec_ev.
          rename t2 into impl_ev.
          rename Heqp into HSpec.
          rename Heqp3 into HImpl.
          rename Heqp5 into HImplStep.
          rename Heqp1 into HSpecStep.

          specialize ModSpec.extract_core0_steps_from_metadata with (1 := HSpec);
          specialize ModImpl.extract_core0_steps_from_metadata with (1 := HImpl); intros HImplCore0 [prop_core0 HSpecCore0].
          specialize ModSpec.extract_core1_steps_from_metadata with (1 := HSpec);
          specialize ModImpl.extract_core1_steps_from_metadata with (1 := HImpl); intros HImplCore1 [prop_core1 HSpecCore1].
          specialize ModSpec.extract_sm_steps_from_metadata with (1 := HSpec);
          specialize ModImpl.extract_sm_steps_from_metadata with (1 := HImpl); intros HImplSM [prop_sm HSpecSM].
          specialize ModSpec.extract_mem_steps_from_metadata with (1 := HSpec);
          specialize ModImpl.extract_mem_steps_from_metadata with (1 := HImpl); intros HImplMem [prop_mem HSpecMem].

          specialize ModSpec.step_n_invariant with (1 := HSpec); intros [HSpecInv HSpecProp]; propositional.
          propositional.


Definition impl_core0_input (impl_io: ModImpl.mod_step_io) : Core_Common.input_t :=
  Core_Common.step_input (ModImpl.step_io_core0 impl_io).
Definition spec_core0_input (spec_io: ModSpec.mod_step_io) : Core_Common.input_t :=
  Core_Common.step_input (ModSpec.step_io_core0 spec_io).
Definition impl_core1_input (impl_io: ModImpl.mod_step_io) : Core_Common.input_t :=
  Core_Common.step_input (ModImpl.step_io_core1 impl_io).
Definition spec_core1_input (spec_io: ModSpec.mod_step_io) : Core_Common.input_t :=
  Core_Common.step_input (ModSpec.step_io_core1 spec_io).


  Ltac fast_destruct_nongoal_matches :=
    repeat (match goal with
            | [ H: context[match ?d with | _ => _ end] |- _ ] =>
                destruct_matches_in d
                end).

Ltac unfold_spec_props :=
  consider ModSpec.valid_props;
  consider ModSpec.valid_P_prop;
  consider ModSpec.core0_P_prop;
  consider ModSpec.core1_P_prop;
  consider ModSpec.sm_P_prop;
  consider ModSpec.mem_P_prop.

Lemma impl_do_step_core0_input_empty :
  forall impl_st impl_st' impl_ev impl_io,
  ModImpl.do_step_with_metadata impl_st = (impl_st', impl_ev, impl_io) ->
  impl_core0_input impl_io = log_empty.
Proof.
  intros.
  consider ModImpl.do_step_with_metadata; consider ModImpl.compute_mod_outputs;
    fast_destruct_nongoal_matches; simplify_tupless; simpl in *.
  consider ModImpl.do_core0; fast_destruct_nongoal_matches; simplify_tupless; simpl in *.
  consider @Core_Common.proj_log__pub.
  apply_equiv_eq.
  consider impl_core0_input.
  intros; autorewrite with log_helpers; auto.
Qed.

Lemma spec_do_step_core0_input_empty :
  forall spec_st spec_st' spec_ev spec_io,
  ModSpec.do_step_with_metadata spec_st = (spec_st', spec_ev, spec_io) ->
  spec_core0_input spec_io = log_empty.
Proof.
  intros.
  consider ModSpec.do_step_with_metadata; consider ModSpec.compute_mod_outputs;
    fast_destruct_nongoal_matches; simplify_tupless; simpl in *.
  consider ModSpec.do_core0; fast_destruct_nongoal_matches; simplify_tupless; simpl in *.
  consider @Core_Common.proj_log__pub.
  apply_equiv_eq.
  intros; autorewrite with log_helpers; auto.
Qed.

Arguments ModImpl.compute_state : simpl never.
Lemma impl_core0_do_step_output :
  forall impl_st impl_st' impl_ev impl_io,
  ModImpl.do_step_with_metadata impl_st = (impl_st', impl_ev, impl_io) ->
  fst (core0_do_step_input__koika (ModImpl.state_core0 impl_st)
                                (impl_core0_input impl_io)) =
  ModImpl.output_core0 impl_ev.
Proof.
  intros.
  consider ModImpl.do_step_with_metadata; consider ModImpl.compute_mod_outputs;
    fast_destruct_nongoal_matches; simplify_tupless.
  simpl.
  consider ModImpl.do_core0; fast_destruct_nongoal_matches; simplify_tupless; simpl.
  unfold_core0_steps.
  autorewrite with log_helpers in *.
  consider @Core_Common.do_step_input__koika; simplify_tupless.
  auto.
Qed.

Lemma spec_core0_do_step_output :
  forall spec_st spec_st' spec_ev spec_io,
  ModSpec.do_step_with_metadata spec_st = (spec_st', spec_ev, spec_io) ->
  fst (core0_do_step_trans_input__spec (ModSpec.state_core0 spec_st) (spec_core0_input spec_io)) =
  ModSpec.output_core0 spec_ev.
Proof.
  intros.
  consider ModSpec.do_step_with_metadata; consider ModSpec.compute_mod_outputs;
    fast_destruct_nongoal_matches; simplify_tuples.
  consider ModSpec.do_core0; fast_destruct_nongoal_matches; simplify_tupless.
  unfold_core0_steps.
  autorewrite with log_helpers in *.
  consider @Core_Common.proj_log__pub.
  consider @Core_Common.do_step_trans_input__spec; consider @Core_Common.do_step_input__koika; simplify_tupless.
  simpl.
  consider spec_core0_input; simpl.
  auto.
Qed.
Hint Rewrite @SemanticProperties.log_app_empty_l : log_helpers.
Lemma impl_core1_do_step_input :
  forall impl_st impl_st' impl_ev impl_io,
  ModImpl.do_step_with_metadata impl_st = (impl_st', impl_ev, impl_io) ->
  impl_core1_input impl_io =
    Core_Common.proj_log__pub
      (proj_log (REnv' := ContextEnv) Impl.System.Lift_core1 (lift_log Impl.System.Lift_core0 (ModImpl.output_core0 impl_ev))).
Proof.
  intros.
  consider impl_core1_input; simpl.
  consider ModImpl.do_step_with_metadata; consider ModImpl.compute_mod_outputs;
    fast_destruct_nongoal_matches; simplify_tupless; simpl.
  consider ModImpl.do_core1; fast_destruct_nongoal_matches; simplify_tupless; simpl.
  consider ModImpl.do_core0; destruct_all_matches; simplify_tupless.
  autorewrite with log_helpers; auto.
Qed.

Lemma spec_core1_do_step_input :
  forall spec_st spec_st' spec_ev spec_io,
  ModSpec.do_step_with_metadata spec_st = (spec_st', spec_ev, spec_io) ->
  spec_core1_input spec_io =
    Core_Common.proj_log__pub
      (proj_log (REnv' := ContextEnv) Impl.System.Lift_core1 (lift_log Impl.System.Lift_core0 (ModSpec.output_core0 spec_ev))).
Proof.
  intros.
  consider spec_core1_input; simpl.
  consider ModSpec.do_step_with_metadata; consider ModSpec.compute_mod_outputs;
    fast_destruct_nongoal_matches; simplify_tupless; simpl.
  consider ModSpec.do_core1; fast_destruct_nongoal_matches; simplify_tupless; simpl.
  consider ModSpec.do_core0; fast_destruct_nongoal_matches; simplify_tupless; simpl.
  autorewrite with log_helpers.
  auto.
Qed.


          (* ======== Equiv inputs/outputs, forward ========= *)
          assert (impl_core0_input impl_io = log_empty) as HImplCore0Empty
             by (eapply impl_do_step_core0_input_empty; eauto).
          assert (spec_core0_input spec_io = log_empty) as HSpecCore0Empty
             by (eapply spec_do_step_core0_input_empty; eauto).
          (* Core0 input *)
          assert (impl_core0_input impl_io = spec_core0_input spec_io) as Heq_core0_input.
          { rewrite_solve. }
          (* Core0 output *)
          assert (core0_output_log_equivalent (ModImpl.output_core0 impl_ev)
                                              (ModSpec.output_core0 spec_ev)).
          { rewrite forall_sim_step_extract_core0 with (1 := IHn) in *.
            consider core0_output_log_equivalent.
            eapply Core0.output_correctness with (input := impl_core0_input impl_io); eauto.
            - rewrite_term_from_tuple prop_core0; unfold_spec_props; intuition.
            - rewrite_term_from_tuple prop_core0; unfold_spec_props; intuition.
            - rewrite<-impl_core0_do_step_output with (1 := HImplStep); auto.
            - rewrite<-spec_core0_do_step_output with (1 := HSpecStep); unfold_core0_steps; rewrite_solve.
          }
          (* Core1 input *)
          assert (impl_core1_input impl_io = spec_core1_input spec_io).
          {
            rewrite impl_core1_do_step_input with (1 := HImplStep).
            rewrite spec_core1_do_step_input with (1 := HSpecStep).
            consider core0_output_log_equivalent.
            consider @Core_Common.output_log_equivalent.

            consider @Core_Common.ext_log_equivalent.



          }
          assert (SM_Common.step_input (ModImpl.step_io_sm impl_io)
                  = SM_Common.step_input (fst (ModSpec.step_io_sm spec_io))) by admit.
          assert (Mem_Common.step_input (ModImpl.step_io_mem impl_io)
                  = Mem_Common.step_input (Mem_Common.ghost_step (ModSpec.step_io_mem spec_io))) by admit.

          (* ======= Equiv feedback, backwards ====== *)
          assert (Mem_Common.step_feedback (ModImpl.step_io_mem impl_io)
                  = Mem_Common.step_feedback (Mem_Common.ghost_step (ModSpec.step_io_mem spec_io))) by admit.
          assert (SM_Common.step_feedback (ModImpl.step_io_sm impl_io)
                  = SM_Common.step_feedback (fst (ModSpec.step_io_sm spec_io))) by admit.
          assert (Core_Common.step_feedback (ModImpl.step_io_core1 impl_io)
                  = Core_Common.step_feedback (ModSpec.step_io_core1 spec_io)) by admit.
          assert (Core_Common.step_feedback (ModImpl.step_io_core0 impl_io)
                  = Core_Common.step_feedback (ModSpec.step_io_core0 spec_io)) by admit.

          (* ======= Solve ====== *)
          constructor;
            destruct impl_io; destruct spec_io; simpl in *;
            match goal with
            | |- ?x = ?y => destruct x; destruct y
            end; simpl in *; rewrite_solve.

      Admitted.

      Definition TODO_sm_trace_equivalent :=
        @SM_Common.trace_equivalent Params0.initial_pc Params1.initial_pc
                                    EnclaveParams.params External.ext.

      Inductive GenTraceSim (impl_tr: ModImpl.trace) (spec_tr: ModSpec.trace) :=
      | _SimTrace :
          forall (core0_sim: (@Core_Common.trace_equivalent Core0.private_params)
                          (map ModImpl.output_core0 impl_tr)
                          (map ModSpec.output_core0 spec_tr))
            (core1_sim: (@Core_Common.trace_equivalent Core1.private_params)
                          (map ModImpl.output_core1 impl_tr)
                          (map ModSpec.output_core1 spec_tr))
            (sm_sim: TODO_sm_trace_equivalent
                       (map ModImpl.output_sm impl_tr)
                       (map ModSpec.output_sm spec_tr))
            (mem_sim: (@Mem_Common.trace_equivalent Memory.private_params)
                        (map ModImpl.output_mem impl_tr)
                        (map ModSpec.output_mem spec_tr)),
          GenTraceSim impl_tr spec_tr.

    End Simulation.

    Definition tau_related : ModImpl.tau -> ModSpec.tau -> Prop :=
      fun impl_ev spec_ev =>
      generate_observations__modImpl impl_ev = generate_observations__modSpec spec_ev.

    Definition trace_related : ModImpl.trace -> ModSpec.trace -> Prop :=
      fun impl_tr spec_tr => List.Forall2 tau_related impl_tr spec_tr.

    Lemma GenTraceSim_impl_trace_related :
      forall impl_tr spec_tr,
      GenTraceSim impl_tr spec_tr ->
      trace_related impl_tr spec_tr.
    Proof.
    Admitted.
    Theorem refinement :
      forall (initial_dram: dram_t) (n: nat)
        (impl_st: ModImpl.state) (impl_tr: ModImpl.trace)
        (spec_st: ModSpec.state) (spec_tr: ModSpec.trace),
      ModImpl.step_n initial_dram n = (impl_st, impl_tr) ->
      ModSpec.step_n initial_dram n = (spec_st, spec_tr) ->
      trace_related impl_tr spec_tr.
    Proof.
      intros *; intros HImplStep; intros HSpecStep.
      apply ModImpl.step_n_extract_ios in HImplStep.
      apply ModSpec.step_n_extract_ios in HSpecStep.
      propositional.
      specialize ModImpl.step_rel_decoupled_step__state with (1 := HImplStep0); intro HImplState.
      specialize ModSpec.step_rel_decoupled_step__state with (1 := HSpecStep0); intro HSpecState.
      specialize ModImpl.step_rel_decoupled_step__trace with (1 := HImplStep0); intro HImplTrace.
      specialize ModSpec.step_rel_decoupled_step__trace with (1 := HSpecStep0); intro HSpecTrace.
      apply GenTraceSim_impl_trace_related.
      specialize step_n_ios_sim with (1 := HImplStep0) (2 := HSpecStep0); intros HSim.
      specialize ModSpec.step_n_invariant with (1 := HSpecStep0); intros [HSpecInv HSpecProp]; propositional.

      constructor.
      - specialize ModSpec.extract_core0_steps_from_metadata with (1 := HSpecStep0);
        specialize ModImpl.extract_core0_steps_from_metadata with (1 := HImplStep0); intros.
        propositional.
        unfold_core0_steps.
        rewrite forall_sim_step_extract_core0 with (1 := HSim) in *.
        eapply Core0.correctness; eauto;
          rewrite_term_from_tuple props; unfold_spec_props; intuition.
      - specialize ModSpec.extract_core1_steps_from_metadata with (1 := HSpecStep0);
        specialize ModImpl.extract_core1_steps_from_metadata with (1 := HImplStep0); intros.
        propositional.
        unfold_core1_steps.
        rewrite forall_sim_step_extract_core1 with (1 := HSim) in *.
        eapply Core1.correctness; eauto;
          rewrite_term_from_tuple props; unfold_spec_props; intuition.
      - specialize ModSpec.extract_sm_steps_from_metadata with (1 := HSpecStep0);
        specialize ModImpl.extract_sm_steps_from_metadata with (1 := HImplStep0); intros.
        propositional.
        unfold_sm_steps.
        rewrite forall_sim_step_extract_sm with (1 := HSim) in *.
        eapply SM_Common.correctness; eauto;
          rewrite_term_from_tuple props; unfold_spec_props; intuition.
      - specialize ModSpec.extract_mem_steps_from_metadata with (1 := HSpecStep0);
        specialize ModImpl.extract_mem_steps_from_metadata with (1 := HImplStep0); intros.
        propositional.
        unfold_mem_steps.
        rewrite forall_sim_step_extract_mem with (1 := HSim) in *.
        eapply Memory.correctness; eauto;
          rewrite_term_from_tuple props; unfold_spec_props; intuition.
    Qed.

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

  Module ImplToModImpl.
    Import Observations.
    Import Interfaces.Common.

    Section GeneralizeImpl.
      Definition gen_impl_tau : Type := Log Impl.System.R ContextEnv * Impl.external_state_t.
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
          forall (log_sim: fst gen_ev = ModImpl.outputs_to_impl_log mod_ev),
            (* (mem_ext_st_sm : snd gen_ev = snd (ModImpl.output_mem mod_ev)), *)
          GenTauSim gen_ev mod_ev.

      Definition GenTraceSim (gen_tr: gen_impl_trace) (mod_tr: ModImpl.trace) : Prop :=
        Forall2 GenTauSim gen_tr mod_tr.

      Local Hint Constructors Sim : core.
      Local Hint Constructors GenTauSim : core.
      Local Hint Unfold GenTraceSim : core.

      (* TODO: Move to better place *)
      Local Hint Resolve wf_r_lift_core0 : core.
      Local Hint Resolve wf_r_lift_core1 : core.
      Local Hint Resolve wf_r_lift_sm : core.
      Local Hint Resolve wf_r_lift_mem : core.
      Local Hint Resolve wf_core0_Sigma : core.
      Local Hint Resolve wf_core0_sigma : core.
      Local Hint Resolve wf_core1_Sigma : core.
      Local Hint Resolve wf_core1_sigma : core.
      Local Hint Unfold core0_empty_private_regs : log_helpers.
      Local Hint Unfold core1_empty_private_regs : log_helpers.
      Local Hint Unfold sm_empty_private_regs : log_helpers.
      Local Hint Unfold mem_empty_private_regs : log_helpers.
      Local Hint Resolve equivalent_rules_core0_lift : core.
      Local Hint Resolve equivalent_rules_core1_lift : core.
      Local Hint Resolve equivalent_rules_sm_lift : core.
      Local Hint Resolve equivalent_rules_sm_lift : core.

      Hint Rewrite @SemanticProperties.log_app_empty_l
                   @SemanticProperties.log_app_empty_r
                   : log_helpers.


      Lemma initial_state_sim (initial_dram: dram_t):
        Sim (Impl.initial_state initial_dram) (ModImpl.initial_state initial_dram).
      Proof.
        constructor; simpl; unfold_get_impls.
        4: apply f_equal2; auto.
        all: apply equiv_eq; unfold equiv, proj_env; intros;
             repeat (autorewrite with log_helpers; simpl; auto).
      Qed.


      Ltac solve_not_exists_lift_to_private :=
        match goal with
        | |- not (exists reg, _ reg = Impl.System.Core0_private _) =>
          clear; intros; intuition; solve[repeat (destruct_one_ind; try discriminate)]
        | |- not (exists reg, _ reg = Impl.System.Core1_private _) =>
          clear; intros; intuition; solve[repeat (destruct_one_ind; try discriminate)]
        | |- not (exists reg, _ reg = Impl.System.SM_private _) =>
          clear; intros; intuition; solve[repeat (destruct_one_ind; try discriminate)]
        | |- not (exists reg, _ reg = Impl.System.Mem_private _) =>
          clear; intros; intuition; solve[repeat (destruct_one_ind; try discriminate)]
        end.

      Hint Extern 10 => solve_not_exists_lift_to_private : log_helpers.

      Ltac destruct_and_rewrite_Hsim :=
        match goal with
        | H: Sim _ _ |- _  =>
          destruct H as [?core0_sim ?core1_sim ?sm_sim ?mem_sim];
          consider get_impl_core0;
          consider get_impl_core1;
          consider get_impl_sm;
          consider get_impl_mem;
          consider get_impl_koika_mem;
          rewrite<-core0_sim in *;
          rewrite<-core1_sim in *;
          rewrite<-sm_sim in *;
          rewrite<-mem_sim in *
        end.

      Ltac bash_step :=
        match goal with
        | |- _ => progress simpl
        | |- _ => progress auto_with_log_helpers
        | |- _ => progress (try unfold eq_rect_r in *; simpl_eqs)
        | |- context[getenv _ (log_app _ _ )] =>
          rewrite getenv_logapp
        | |- _ => progress simplify_tuples; subst
        end.

      Hint Rewrite @getenv_lift_log_not_exists using (solve[auto_with_log_helpers]) : log_helpers.
      Hint Rewrite @lift_log_app : log_helpers.
      Hint Rewrite<-@SemanticProperties.log_app_assoc : log_helpers.

      Ltac solve_getenv_lift_log_not_exists :=
        repeat match goal with
        | |- getenv _ (lift_log _ _ ) = [] =>
            rewrite getenv_lift_log_not_exists; auto
        | |- context[getenv _ (interp_scheduler_delta _ _ (lift_rule ?lift _) _ _ ) _] =>
          erewrite<-lift_proj_interp_scheduler_delta with (Rlift := lift); eauto;
            try typeclasses eauto; auto_with_log_helpers
        end.

      (* TODO: goal vs hypothesis pattern? *)
      Ltac do_rewrites :=
        match goal with
        | H: context[Core_Common.lift_ext_log (Core_Common.proj_log__pub _)] |- _ =>
          rewrite core0_lift_ext_log_cancels_proj in H; [ | solve[solve_getenv_lift_log_not_exists; repeat bash_step]]
        (* | H: context[Core_Common.lift_ext_log (Core_Common.proj_log__pub _)] |- _ => *)
        (*   rewrite core1_lift_ext_log_cancels_proj in H; [ | solve[solve_getenv_lift_log_not_exists; repeat bash_step]] *)
        | H: context[SM_Common.lift_ext_log (SM_Common.proj_log__pub _)] |- _ =>
          rewrite sm_lift_ext_log_cancels_proj in H; [ | solve[solve_getenv_lift_log_not_exists;repeat bash_step]]
        | H: context[Mem_Common.lift_ext_log (Mem_Common.proj_log__pub _)] |- _ =>
          rewrite mem_lift_ext_log_cancels_proj in H; [ | solve[solve_getenv_lift_log_not_exists;repeat bash_step]]
        | H: context[log_app (interp_scheduler_delta (proj_env _ _) _ _ (proj_log _ _) _) (proj_log _ _)] |- _ =>
          erewrite log_app_interp_scheduler_delta_proj_comm_proj_interp_scheduler' in H;
            eauto; try typeclasses eauto
        | H: context[interp_scheduler_delta (proj_env _ _) _ _ (proj_log _ _) _] |- _ =>
          erewrite interp_scheduler_delta_comm_proj in H; try typeclasses eauto; eauto
        | |- context[interp_scheduler_delta (proj_env _ _) _ _ (proj_log _ _) _]  =>
          erewrite interp_scheduler_delta_comm_proj ; try typeclasses eauto; eauto
        | H: context[interp_scheduler' (proj_env _ _) _ _ (proj_log _ _) _] |- _ =>
          erewrite interp_scheduler'_comm_proj in H; try typeclasses eauto; eauto
        | |- context[interp_scheduler' (proj_env _ _) _ _ (proj_log _ _) _]  =>
          erewrite interp_scheduler'_comm_proj;  try typeclasses eauto; eauto
        | H: context[lift_log _ (log_app _ _)] |- _ =>
          rewrite lift_log_app in H
        | |- context[lift_log _ (log_app _ _)]  =>
          rewrite lift_log_app
        | H: context[lift_log ?lift (proj_log ?lift _)] |- _ =>
          rewrite lift_log_proj_inv in H;
            [ | solve[(eapply wf_interp_scheduler_delta_on_lifted_rules; eauto with log_helpers) ||
                      (intros; setoid_rewrite wf_interp_scheduler'_with_lifted_rules; auto_with_log_helpers)]]
        | |- context[lift_log ?lift (proj_log ?lift _)]  =>
          rewrite lift_log_proj_inv ;
            [ | solve[(eapply wf_interp_scheduler_delta_on_lifted_rules; eauto with log_helpers) ||
                      (intros; setoid_rewrite wf_interp_scheduler'_with_lifted_rules; auto_with_log_helpers)]]
        end.


      Hint Rewrite core0_lift_ext_log_cancels_proj using (solve[repeat bash_step; solve_getenv_lift_log_not_exists]): log_helpers.
      Hint Rewrite core1_lift_ext_log_cancels_proj using (solve[repeat bash_step; solve_getenv_lift_log_not_exists]): log_helpers.
      Hint Rewrite sm_lift_ext_log_cancels_proj using (solve[repeat bash_step; solve_getenv_lift_log_not_exists]) : log_helpers.
      Hint Rewrite mem_lift_ext_log_cancels_proj using (solve[repeat bash_step; solve_getenv_lift_log_not_exists]) : log_helpers.

      Ltac quick_cleanup :=
        match goal with
        | |- context[interp_scheduler_delta (proj_env ?lift ?env) ?s ?r log_empty ?sc] =>
            replace (interp_scheduler_delta (proj_env lift env) s r log_empty sc) with
                    (interp_scheduler_delta (REnv := ContextEnv) (proj_env lift env) s r
                                            (proj_log (REnv' := ContextEnv) lift log_empty) sc) by
              (rewrite proj_log_empty; auto)
        | |- context[interp_scheduler' (proj_env ?lift ?env) ?s ?r log_empty ?sc] =>
            replace (interp_scheduler' (proj_env lift env) s r log_empty sc) with
                    (interp_scheduler' (REnv := ContextEnv) (proj_env lift env) s r
                                            (proj_log (REnv' := ContextEnv) lift log_empty) sc) by
              (rewrite proj_log_empty; auto)
        | H: context[lift_log _ (log_app _ _)] |- _ =>
            rewrite lift_log_app in H
        | |- context[lift_log _ (log_app _ _)] =>
            rewrite lift_log_app
        | H: context[log_app (proj_log _ _) (proj_log _ _)] |- _ =>
            rewrite log_app_comm_proj_log in H
        | |- context[log_app (proj_log _ _) (proj_log _ _)] =>
            rewrite log_app_comm_proj_log
        end.

      Ltac remove_deltas :=
        match goal with
        | H: context[log_app (interp_scheduler_delta _ _ _ ?sched_log _) ?sched_log] |- _ =>
            rewrite<-interp_scheduler_delta_correspond_to_interp_scheduler in H
        | |- context[log_app (interp_scheduler_delta _ _ _ ?sched_log _) ?sched_log] =>
            rewrite<-interp_scheduler_delta_correspond_to_interp_scheduler
        | H: context[interp_scheduler_delta _ _ _ log_empty _ ] |- _ =>
            rewrite<-interp_scheduler_delta_correspond_to_interp_scheduler_empty in H
        | |- context[interp_scheduler_delta _ _ _ log_empty _ ] =>
            rewrite<-interp_scheduler_delta_correspond_to_interp_scheduler_empty
      end.

      Hint Rewrite<-@interp_scheduler_delta_correspond_to_interp_scheduler_empty : log_helpers.
      Hint Rewrite<-@interp_scheduler_delta_correspond_to_interp_scheduler : log_helpers.
      Hint Rewrite @log_app_comm_proj_log : log_helpers.

      Axiom __magic : forall T, T.

      Theorem step_sim : forall (impl_st impl_st': Impl.state) (mod_st mod_st': ModImpl.state)
                           (impl_ev: gen_impl_tau) (mod_ev: ModImpl.tau),
        Sim impl_st mod_st ->
        gen_impl_step impl_st = (impl_st', impl_ev) ->
        ModImpl.do_step mod_st = (mod_st', mod_ev) ->
        Sim impl_st' mod_st' /\ GenTauSim impl_ev mod_ev.
      Proof.
        intros *; intros HSim HGenStep HModStep.
        consider gen_impl_step.
        destruct_one_match_in HGenStep.
        consider Impl.update_function.
        destruct_one_match_in HGenStep0.
        remember (Impl.update_koika (Impl.koika_state impl_st)) as UpdateKoika.
        consider Impl.update_koika.
        consider Impl.System.schedule.
        consider @interp_scheduler.

        consider Impl.System.sigma.
        (* consider Impl.System.rule_name_t. *)
        consider Impl.update_external_st.

        repeat rewrite interp_scheduler'_app in HeqUpdateKoika.

        consider ModImpl.do_step.
        repeat (destruct_one_match_in HModStep; destruct_pairs).

        destruct_and_rewrite_Hsim.


        erewrite<-interp_scheduler'_rules_equiv with (1 := equivalent_rules_core0_lift Core0.schedule)
          in HeqUpdateKoika.
        erewrite<-interp_scheduler'_rules_equiv with (1 := equivalent_rules_core1_lift Core1.schedule)
          in HeqUpdateKoika.
        erewrite<-interp_scheduler'_rules_equiv with (1 := equivalent_rules_sm_lift SM_Common.schedule)
          in HeqUpdateKoika.
        erewrite<-interp_scheduler'_rules_equiv with (1 := equivalent_rules_mem_lift Memory.schedule)
          in HeqUpdateKoika.
        simpl in *.

        consider ModImpl.do_core0.
        destruct_all_matches.
        consider core0_do_step__koika.
        consider core0_do_step_input__koika.
        (* consider Impl.System.core0_schedule. *)
        consider Core0.rule.
        consider Core0.sigma.

        consider ModImpl.do_core1.
        destruct_all_matches.
        consider core1_do_step__koika.
        consider core1_do_step_input__koika.
        (* consider Core1.update_function.  *)
        (* consider Impl.System.core1_schedule. *)
        consider Core1.rule.
        consider Core1.sigma.

        consider @Core_Common.do_step__koika.
        consider @Core_Common.do_step_input__koika.
        consider @Core_Common.update_function.

        repeat do_rewrites.

        consider ModImpl.do_sm.
        destruct_all_matches.
        consider Impl.System.SM.do_step_input__impl.
        consider Impl.System.SM.do_step__impl.
        consider @SM_Common.do_step_input__impl.
        consider @SM_Common.update_function.

        consider ModImpl.do_mem.
        destruct_all_matches.
        consider mem_do_step__impl.
        consider @Mem_Common.do_step__impl.
        consider mem_do_step_input__impl.
        consider @Mem_Common.do_step_input__impl.

        consider @Mem_Common.update_function.
        destruct_all_matches.
        consider @Mem_Common.koika_update_function.
        consider Memory.rule.

        (* repeat (rewrite core0_lift_ext_log_cancels_proj in *; *)
        (*           [ | solve[solve_getenv_lift_log_not_exists; repeat bash_step]]); *)
        (* repeat (rewrite sm_lift_ext_log_cancels_proj in *; *)
        (*          [ | solve[solve_getenv_lift_log_not_exists;repeat bash_step]]). *)
        repeat do_rewrites.
        (* repeat do_rewrites. (* TODO: speed this up *) *)
        (* repeat rewrite<-interp_scheduler_delta_correspond_to_interp_scheduler in *. *)
        simplify_tuples; subst; simpl in *.
        repeat quick_cleanup.
        repeat remove_deltas.

        repeat match goal with
        | |- context[lift_log ?x ?y] =>
            remember (lift_log x y)
        end.

        (* repeat quick_cleanup. *)
        (* repeat remove_deltas. *)
        (* simpl in *; subst. *)
        autorewrite with log_helpers in *. (* slightly slow *)
        repeat do_rewrites.

        (* replace (Impl.System.FnLift_core1) with Impl.System.FnLift_core0 in * by auto. *)

        repeat remove_deltas.
        simpl in *; subst.
        autorewrite with log_helpers in *.
        setoid_rewrite Heqp0 in Heqp5; simplify_tuples; subst.
        setoid_rewrite Heqp0 in Heqp4; simplify_tuples; subst.
        split.
        { repeat quick_cleanup.
          auto_with_log_helpers.
          repeat quick_cleanup.
          repeat remove_deltas.
          repeat do_rewrites.
          autorewrite with log_helpers.
          repeat rewrite log_app_comm_proj_log.
          auto_with_log_helpers.
          replace (Impl.System.FnLift_core1) with Impl.System.FnLift_core0 in * by auto.
          repeat remove_deltas.
          repeat rewrite commit_update_comm_proj_env.
          constructor; simpl.
          { auto. }
          { auto. }
          { auto. }
          { unfold get_impl_mem; simpl.
            f_equal; auto.
            { unfold get_impl_koika_mem.
              replace l6 with (proj_log (REnv := ContextEnv) (REnv' := ContextEnv) Impl.System.Lift_mem
                                        (lift_log (REnv := ContextEnv) Impl.System.Lift_mem l6)) at 2
                by (apply proj_log_lift_inv).
              rewrite log_app_comm_proj_log.
              rewrite commit_update_comm_proj_env.
              auto.
            }
          }
        }
        { simpl; subst.
          autorewrite with log_helpers in *.
          repeat do_rewrites.
          repeat remove_deltas.
          constructor; simpl; auto.
          { consider ModImpl.outputs_to_impl_log; simpl.
            autorewrite with log_helpers.
            repeat do_rewrites.
            auto_with_log_helpers.
            repeat remove_deltas.
            auto_with_log_helpers.
          }
        }
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
        rewrite log_sim. auto.
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

End TradPf.
