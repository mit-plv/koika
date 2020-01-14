(*! ORAAT | Proof of the One-rule-at-a-time theorem !*)
Require Import
        Koika.Common Koika.Syntax Koika.TypedSyntax
        Koika.TypedSyntaxFunctions Koika.SemanticProperties.
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Ring Coq.setoid_ring.Ring.

Open Scope bool_scope.

Section Proof.
  Context {pos_t var_t rule_name_t reg_t ext_fn_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.

  Context {R: reg_t -> type}.
  Context {Sigma: ext_fn_t -> ExternalSignature}.
  Context {REnv: Env reg_t}.
  Context (r: REnv.(env_t) R).
  Context (sigma: forall f, Sig_denote (Sigma f)).

  Notation Log := (Log R REnv).
  Notation action := (action pos_t var_t R Sigma).
  Notation rule := (rule pos_t var_t R Sigma).
  Notation scheduler := (scheduler pos_t rule_name_t).

  Context (rules: rule_name_t -> rule).

  Fixpoint interp_scheduler'_trace
           (sched_log: Log)
           (s: scheduler)
           {struct s} :=
    let interp_try rl s1 s2 :=
        match interp_rule r sigma sched_log (rules rl) with
        | Some l => match interp_scheduler'_trace (log_app l sched_log) s1 with
                   | Some (rs, log) => Some (rl :: rs, log)
                   | None => None
                   end
        | None => interp_scheduler'_trace sched_log s2
        end in
    match s with
    | Done => Some ([], sched_log)
    | Cons rl s => interp_try rl s s
    | Try rl s1 s2 => interp_try rl s1 s2
    | SPos _ s => interp_scheduler'_trace sched_log s
    end.

  Definition interp_scheduler_trace_and_update
        l
        (s: scheduler) :=
    match interp_scheduler'_trace l s with
    | Some (rs, log) => Some (rs, commit_update r log)
    | None => None
    end.

  Definition update_one r rl: option (REnv.(env_t) R) :=
    let/opt r := r in
    let log := @interp_scheduler'
                pos_t var_t rule_name_t reg_t ext_fn_t
                R Sigma REnv r sigma rules
                log_empty (Try rl Done Done) in
    Some (commit_update r log).

  Notation latest_write l idx := (latest_write (RKind_denote := type_denote) (_R := R) (REnv := REnv) l idx).

  Ltac set_forallb_fns :=
    repeat match goal with
           | [  |- context[log_forallb _ _ ?fn] ] =>
             match fn with
             | (fun _ => _) => set fn
             end
           end.

  Lemma may_read_app_sl :
    forall (sl sl': Log) prt idx,
      may_read (log_app sl sl') prt idx =
      may_read sl prt idx && may_read sl' prt idx.
  Proof.
    unfold may_read; intros.
    destruct prt; rewrite !log_forallb_not_existsb, !log_forallb_app;
      ring_simplify; f_equal.
  Qed.

  Lemma may_write_app_sl :
    forall (sl sl': Log) l prt idx,
      may_write (log_app sl sl') l prt idx =
      may_write sl l prt idx && may_write sl' l prt idx.
  Proof.
    unfold may_write; intros.
    destruct prt; rewrite !log_forallb_not_existsb, !log_forallb_app;
      ring_simplify;
      repeat (destruct (log_forallb _ _ _); cbn; try reflexivity).
  Qed.

  Ltac bool_step :=
    match goal with
    | _ => progress Common.bool_step
    | [ H: log_forallb (log_app _ _) _ _ = _ |- _ ] =>
      rewrite log_forallb_app in H
    end.

  Lemma may_read0_no_writes :
    forall sl idx,
      may_read sl P0 idx = true ->
      latest_write sl idx = None.
  Proof.
    unfold may_read; intros.
    rewrite !log_forallb_not_existsb in H.
    repeat (cleanup_step || bool_step).
    unfold log_forallb in *.
    rewrite forallb_forall in *.
    unfold is_write0, is_write1, latest_write, log_find in *.
    apply find_none_notb.
    intros a HIn.
    repeat match goal with
           | [ H: forall (_: LogEntry _), _ |- _ ] => specialize (H a HIn)
           end.
    destruct a; cbn in *; destruct kind; subst; try reflexivity.
    destruct port; cbn in *; try discriminate.
  Qed.

  Lemma may_read1_latest_write_is_0 :
    forall (l: Log) idx,
      may_read l P1 idx = true ->
      latest_write l idx = latest_write0 l idx.
  Proof.
    unfold may_read, latest_write, latest_write0, log_find, log_forallb.
    intros * H.
    rewrite log_forallb_not_existsb in H; unfold log_forallb in H.
    set (getenv REnv l idx) as ls in *; cbn in *; clearbody ls.
    set (R idx) as t in *; cbn in *.
    revert H.
    induction ls.
    - reflexivity.
    - intros * H; cbn in H.
      repeat (bool_step || cleanup_step).
      rewrite (IHls ltac:(eassumption)).
      unfold log_latest_write_fn; cbn.
      destruct a, kind, port; try discriminate; reflexivity.
  Qed.

  Create HintDb oraat.
  Hint Unfold interp_rule : oraat.

  Ltac t_step :=
    match goal with
    | _ => cleanup_step
    | _ => progress autounfold with oraat in *
    | [ H: context[may_read (log_app _ _) _ _] |- _ ] =>
      rewrite may_read_app_sl in H
    | [ H: context[may_write (log_app _ _) _ _ _] |- _ ] =>
      rewrite may_write_app_sl in H
    | [ H: Some _ = Some _ |- _ ] =>
      inversion H; subst; clear H
    | [ H: opt_bind ?x _ = Some _ |- _ ] =>
      destruct x eqn:?; cbn in H; try discriminate
    | [ H: match ?x with _ => _ end = Some _ |- _ ] =>
      destruct x eqn:?; subst; cbn in H; try discriminate
    | _ =>
      bool_step
    | [ H: match ?x with _ => _ end = ?c |- _ ] =>
      let c_hd := constr_hd c in
      is_constructor c_hd; destruct x eqn:?
    | [ H: ?x = _ |- context[match ?x with _ => _ end] ] =>
      rewrite H
    | [ H: context[_ -> interp_action _ _ _ _ _ ?a = Some _] |- _ ] =>
      erewrite H by eauto
    | _ => reflexivity
    end.

  Ltac t :=
    repeat t_step.

  Lemma interp_action_commit:
    forall {sig tau} (a: action sig tau) (Gamma: tcontext sig) (sl sl': Log) action_log lv,
      interp_action r sigma Gamma (log_app sl sl') action_log a = Some lv ->
      interp_action (commit_update r sl') sigma Gamma sl action_log a = Some lv.
  Proof.
    induction a; cbn; intros Gamma sl sl' action_log lv HSome; try congruence.
    - (* Assign *) t.
    - (* Seq *) t.
    - (* Bind *) t.
    - (* If *) t.
    - destruct port; t.
      + (* Read0 *)
        erewrite getenv_commit_update by eassumption.
        erewrite may_read0_no_writes by eauto.
        reflexivity.
      + (* Read1 *)
        rewrite log_app_assoc.
        rewrite (latest_write0_app (log_app action_log sl) sl').
        destruct latest_write0.
        * reflexivity.
        * erewrite getenv_commit_update by eassumption.
          rewrite may_read1_latest_write_is_0 by eassumption.
          reflexivity.
    - (* Write *) t.
    - (* UnOp *) t.
    - (* BinOp *) t.
    - (* ExternalCall *) t.
    - (* APos *) t.
  Qed.

  Lemma OneRuleAtATime':
    forall s rs r' l0,
      interp_scheduler_trace_and_update l0 s = Some (rs, r') ->
      List.fold_left (update_one) rs (Some (commit_update r l0)) = Some r'.
  Proof.
    induction s; cbn;
      unfold interp_scheduler_trace_and_update; cbn.
    - (* Done *) inversion 1; subst; cbn in *; eauto.
    - (* Cons *) intros; t.
      + erewrite interp_action_commit by (rewrite log_app_empty_r; eassumption);
          cbn.
        rewrite log_app_empty_l.
        rewrite commit_update_assoc.
        eapply IHs.
        unfold interp_scheduler_trace_and_update.
        rewrite Heqo1; reflexivity.
      + eapply IHs.
        unfold interp_scheduler_trace_and_update; rewrite Heqo.
        reflexivity.
    - (* Try *) intros; t.
      + erewrite interp_action_commit by (rewrite log_app_empty_r; eassumption);
          cbn.
        rewrite log_app_empty_l.
        rewrite commit_update_assoc.
        eapply IHs1.
        unfold interp_scheduler_trace_and_update.
        rewrite Heqo1; reflexivity.
      + eapply IHs2.
        unfold interp_scheduler_trace_and_update; rewrite Heqo.
        reflexivity.
    - (* SPos *) eauto.
  Qed.

  Lemma interp_scheduler_trace_correct :
    forall s l0 log,
      interp_scheduler' r sigma rules l0 s = log ->
      exists rs, interp_scheduler'_trace l0 s = Some (rs, log).
  Proof.
    induction s; cbn.
    - (* Done *) inversion 1; subst; eauto.
    - (* Cons *) intros * Heq. destruct interp_rule as [log' | ] eqn:?.
      + destruct (IHs _ _ Heq) as (rs & Heq').
        rewrite Heq'; eauto.
      + destruct (IHs _ _ Heq) as (rs & Heq').
        rewrite Heq'; eauto.
    - (* Try *) intros * Heq. destruct interp_rule as [log' | ] eqn:?.
      + destruct (IHs1 _ _ Heq) as (rs & Heq').
        rewrite Heq'; eauto.
      + destruct (IHs2 _ _ Heq) as (rs & Heq').
        rewrite Heq'; eauto.
    - (* SPos *) eauto.
  Qed.

  Lemma scheduler_trace_in_scheduler :
    forall s log l0 rs,
      interp_scheduler'_trace l0 s = Some (rs, log) ->
      (forall r : rule_name_t, In r rs -> In r (scheduler_rules s)).
  Proof.
    induction s; cbn in *.
    - (* Done *) inversion 1; subst; inversion 1.
    - (* Cons *) intros * H * H'; t.
      + inversion H'; subst; eauto.
      + eauto.
    - (* Try *) intros * H * H'; rewrite in_app_iff; t.
      + inversion H'; subst; eauto.
      + eauto.
    - (* SPos *) eauto.
  Qed.

  Theorem OneRuleAtATime:
    forall s log,
      interp_scheduler r sigma rules s = log ->
      exists rs,
        (forall rl, List.In rl rs -> List.In rl (scheduler_rules s)) /\
        List.fold_left update_one rs (Some r) = Some (commit_update r log).
  Proof.
    intros * H.
    apply interp_scheduler_trace_correct in H; destruct H as (rs & H).
    exists rs; split.
    - eauto using scheduler_trace_in_scheduler.
    - rewrite <- (commit_update_empty r) at 1.
      eapply OneRuleAtATime'.
      unfold interp_scheduler_trace_and_update; rewrite H; reflexivity.
  Qed.
End Proof.
