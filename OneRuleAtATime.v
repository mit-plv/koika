Require Import SGA.Common SGA.Syntax SGA.Types SGA.Semantics.
Require Import Coq.Lists.List.

Import ListNotations.
Open Scope bool_scope.

Section EnvUpdates.
  Context {reg_t: Type}.
  Context {R: reg_t -> type}.
  Context {REnv: Env reg_t}.

  Definition commit_update r0 (log: Log reg_t R) : REnv.(env_t) R :=
    List.fold_right (fun entry r => match entry with
                                 | LE LogWrite _ idx bs => REnv.(putenv) r idx bs
                                 | _ => r
                                 end)
                    r0 log.

  Lemma commit_update_assoc:
    forall (r : REnv.(env_t) R) (l l' : Log reg_t R),
      commit_update (commit_update r l) l' = commit_update r (l' ++ l).
  Proof.
    unfold commit_update; intros; rewrite fold_right_app; reflexivity.
  Qed.
End EnvUpdates.

Section Proof.
  Context {var_t reg_t fn_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.

  Context {R: reg_t -> type}.
  Context {Sigma: fn_t -> ExternalSignature}.
  Context {REnv: Env reg_t}.
  Context (r: REnv.(env_t) R).
  Context (sigma: forall f, Sigma f).
  Open Scope bool_scope.

  Notation Log := (Log reg_t R).
  Notation expr := (expr var_t R Sigma).
  Notation rule := (rule var_t R Sigma).
  Notation scheduler := (scheduler var_t R Sigma).

  Fixpoint interp_scheduler'_trace
         (sched_log: Log)
         (s: scheduler)
         {struct s} :=
  match s with
  | Done => Some ([], sched_log)
  | Try rl s1 s2 =>
    match interp_rule r sigma CtxEmpty sched_log [] rl with
    | Some l => match interp_scheduler'_trace (l ++ sched_log) s1 with
               | Some (rs, log) => Some (rl :: rs, log)
               | None => None
               end
    | CannotRun => interp_scheduler'_trace sched_log s2
    end
  end.

  Definition interp_scheduler_trace_and_update
        l
        (s: scheduler) :=
    match interp_scheduler'_trace l s with
    | Some (rs, log) => Some (rs, commit_update r log)
    | None => None
    end.

  Definition update_one sigma r rl: option (REnv.(env_t) R) :=
    let/opt rl := rl in
    let/opt log := @interp_scheduler' var_t reg_t fn_t _ R Sigma REnv r sigma [] (Try rl Done Done) in
    Some (commit_update r log).

  Definition latest_write' (l: Log) idx :=
    log_find l idx (fun kind _ => match kind with
                               | LogWrite => true
                               | _ => false
                               end).

  Definition latest_write (log: Log) idx : option (R idx).
  Proof.
    destruct (latest_write' log idx) as [ [ kd pt reg val ] | ] eqn:Heq.
    - unfold latest_write', log_find in Heq.
      apply find_some_transparent in Heq.
      destruct Heq.
      destruct (eq_dec idx reg) in *; try discriminate; subst.
      destruct kd in *; try discriminate; subst.
      exact (Some val).
    - exact None.
  Defined.

  Lemma getenv_commit_update :
    forall sl R idx,
      REnv.(getenv) (commit_update R sl) idx =
      match latest_write sl idx with
      | Some v' => v'
      | None => REnv.(getenv) R idx
      end.
  Proof.
    unfold commit_update; induction sl; cbn; intros.
    - reflexivity.
    - destruct a, kind, PeanoNat.Nat.eq_dec; subst;
        try (erewrite IHsl by eassumption;
             reflexivity).
      + rewrite get_put_eq; reflexivity.
      + rewrite get_put_neq by eauto.
        erewrite IHsl by eassumption.
        reflexivity.
  Qed.

  Lemma bool_result_Success :
    forall b u,
      bool_result b = Success u ->
      b = true.
  Proof.
    destruct b; cbn; congruence.
  Qed.

  Require Import Ring_theory Ring Coq.setoid_ring.Ring.

  Lemma log_forallb_app:
    forall l l' reg (f: LogEntryKind -> Port -> bits -> bool),
      log_forallb (l ++ l') reg f =
      log_forallb l reg f && log_forallb l' reg f.
  Proof.
    unfold log_forallb.
    intros; rewrite !forallb_app; reflexivity.
  Qed.

  Ltac set_forallb_fns :=
    repeat match goal with
           | [  |- context[log_forallb _ _ ?fn] ] =>
             match fn with
             | (fun _ => _) => set fn
             end
           end.

  Lemma may_read0_app_sl :
    forall sl sl' l idx,
      may_read0 (sl ++ sl') l idx =
      may_read0 sl l idx && may_read0 sl' l idx.
  Proof.
    unfold may_read0; intros.
    rewrite !log_forallb_app.
    ring_simplify.
    f_equal.
    f_equal.
    rewrite <- !Bool.andb_assoc.
    rewrite Bool.andb_diag; reflexivity.
  Qed.

  Lemma may_read1_app :
    forall sl sl' idx,
      may_read1 (sl ++ sl') idx =
      may_read1 sl idx && may_read1 sl' idx.
  Proof.
    unfold may_read1; intros.
    rewrite !log_forallb_app.
    reflexivity.
  Qed.

  Lemma may_write_app_sl :
    forall sl sl' l lvl idx,
      may_write (sl ++ sl') l lvl idx =
      may_write sl l lvl idx && may_write sl' l lvl idx.
  Proof.
    unfold may_write; intros.
    destruct lvl; rewrite !log_forallb_app;
      ring_simplify;
      rewrite Bool.andb_diag;
      reflexivity.
  Qed.

  Lemma log_find_in:
    forall l idx P e,
      log_find l idx P = Some e ->
      List.In e l /\ e.(reg) = idx /\ P e.(kind) e.(port) e.(val) = true.
  Proof.
    unfold log_find; intros * H; destruct e; apply find_some in H.
    destruct (PeanoNat.Nat.eq_dec idx reg); subst; cbn in *.
    - intuition eauto.
    - intuition discriminate.
  Qed.

  Lemma find_none_notb {A}:
    forall (P: A -> bool) l,
      (forall a, List.In a l -> P a = false) ->
      find P l = None.
  Proof.
    induction l; cbn; intros * Hnot.
    - reflexivity.
    - pose proof (Hnot a).
      destruct (P a); firstorder discriminate.
  Qed.

  Ltac bool_step :=
    match goal with
    | _ => progress Common.bool_step
    | [ H: log_forallb (_ ++ _) _ _ = _ |- _ ] =>
      rewrite log_forallb_app in H
    end.

  Lemma may_read0_no_writes :
    forall sl l idx,
      may_read0 sl l idx = true ->
      latest_write sl idx = None.
  Proof.
    unfold may_read0; intros.
    repeat (cleanup_step || bool_step).
    unfold log_forallb in *.
    rewrite forallb_forall in *.
    unfold latest_write, log_find.
    apply find_none_notb.
    intros a HIn.
    repeat match goal with
           | [ H: forall (_: LogEntry), _ |- _ ] => specialize (H a HIn)
           end.
    destruct a; cbn in *; destruct PeanoNat.Nat.eq_dec, kind; subst; try reflexivity.
    destruct port; discriminate.
  Qed.

  Lemma find_app {A} :
    forall sl sl' (P: A -> bool),
      find P (sl ++ sl') =
      match find P sl with
      | Some e => Some e
      | None => find P sl'
      end.
  Proof.
    induction sl; cbn; intros.
    - reflexivity.
    - destruct (P a); try rewrite IHsl; reflexivity.
  Qed.

  Lemma log_find_app :
    forall sl sl' idx P,
      log_find (sl ++ sl') idx P =
      match log_find sl idx P with
      | Some e => Some e
      | None => log_find sl' idx P
      end.
  Proof.
    unfold log_find; eauto using find_app.
  Qed.

  Lemma latest_write0_app :
    forall sl sl' idx,
      latest_write0 (sl ++ sl') idx =
      match latest_write0 sl idx with
      | Some e => Some e
      | None => latest_write0 sl' idx
      end.
  Proof.
    unfold latest_write0; eauto using log_find_app.
  Qed.

  Lemma assert_size_success :
    forall v n v',
      assert_size v n = Success v' ->
      v = v' /\ length v' = n.
  Proof.
    unfold assert_size; intros; destruct PeanoNat.Nat.eq_dec;
      firstorder (congruence || discriminate).
  Qed.

  Lemma assert_size_eq :
    forall a n,
      length a = n ->
      assert_size a n = Success a.
  Proof.
    unfold assert_size; intros; destruct PeanoNat.Nat.eq_dec; firstorder.
  Qed.

  Lemma may_read1_latest_write_is_0 :
    forall l idx,
      may_read1 l idx = true ->
      latest_write l idx = latest_write0 l idx.
  Proof.
    induction l.
    - reflexivity.
    - intros * H.
      simpl in H.
      repeat (bool_step || cleanup_step).
      destruct a; cbn; destruct PeanoNat.Nat.eq_dec, kind; cbn;
        try apply (IHl _ ltac:(eassumption)).
      destruct port; cbn in *; try discriminate; reflexivity.
  Qed.

  Lemma fold_left2_result_failure {A B B': Type} (f: A -> B -> B' -> result A) :
    forall (l: list B) (l': list B') (a0: result A),
      a0 = CannotRun \/ a0 = Stuck ->
      fold_left2 (fun acc b b' =>
                    result_bind acc (fun acc =>
                    f acc b b')) l l' a0 = a0.
  Proof.
    induction l; destruct 1; destruct l'; subst; cbn in *; eauto.
  Qed.

  Require Import TypeSafety.

  Lemma log_write_consistent_latest_write :
    forall l (v: fenv nat nat) idx e n,
      log_write_consistent l v ->
      fn v idx n ->
      latest_write l idx = Some e ->
      length (e.(val)) = n.
  Proof.
    intros * Hcst Hin Hwrt.
    pose proof (log_find_in _ _ _ _ Hwrt); cbn in *.
    repeat cleanup_step; destruct e, kind; cbn in *; try discriminate.
    eauto using eq_sym.
  Qed.

  Ltac t_step :=
    match goal with
    | _ => cleanup_step
    | [ H: context[may_read0 (_ ++ _) _ _] |- _ ] =>
      rewrite may_read0_app_sl in H
    | [ H: context[may_read1 (_ ++ _) _] |- _ ] =>
      rewrite may_read1_app in H
    | [ H: context[may_write (_ ++ _) _ _ _] |- _ ] =>
      rewrite may_write_app_sl in H
    | [ H: Success _ = Success _ |- _ ] =>
      inversion H; subst; clear H
    | [ H: bool_result _ = Success _ |- _ ] =>
      apply bool_result_Success in H
    | [ H: opt_result Stuck ?x = Success _ |- _ ] =>
      destruct x eqn:?; subst; cbn in H; try discriminate
    | [ H: result_bind ?x _ = Success _ |- _ ] =>
      destruct x eqn:?; cbn in H; try discriminate
    | [ H: result_map ?x _ = Success _ |- _ ] =>
      destruct x eqn:?; cbn in H; try discriminate
    | [ H: match ?x with _ => _ end = Success _ |- _ ] =>
      destruct x eqn:?; subst; cbn in H; try discriminate
    | [ H: assert_size _ _ = Success _ |- _ ] =>
      apply assert_size_Success in H
    | [ H: env_related (Env := ?Env) ?f ?tenv ?env,
           H': getenv ?env ?k = Some ?v |- _ ] =>
      pose_once (and_fst H k v) H'
    | [ H: env_related ?f ?tenv ?env,
           H': getenv ?env ?k = None |- _ ] =>
      pose_once (and_snd H k) H'
    | _ =>
      bool_step
    | [ H: match ?x with _ => _ end = ?c |- _ ] =>
      let c_hd := constr_hd c in
      is_constructor c_hd; destruct x eqn:?
    | _ => progress (unfold assert_bits in *)
    end.

  Ltac t :=
    repeat t_step.

  Lemma interp_rule_Success_call_consistent:
    forall (args : list (rule var_t fn_t)) (R : env_t REnv) (v : fenv nat nat)
      (Sigma : env_t SigmaEnv) (Gamma : env_t GammaEnv) (sched_log rule_log l : Log) argvs,
      env_related (length (A:=bool)) v R ->
      log_write_consistent rule_log v ->
      Forall
        (fun r : rule var_t fn_t =>
           forall (R : env_t REnv) (v : fenv nat nat) (Sigma : env_t SigmaEnv)
             (Gamma : env_t GammaEnv) (sl rule_log l : Log) (val : value),
             env_related (length (A:=bool)) v R ->
             log_write_consistent rule_log v ->
             interp_rule R Sigma Gamma sl rule_log r = Success (l, val) -> log_write_consistent l v) args ->
      forall (l1 : list bits) (argSizes : list nat),
        length args = length argSizes ->
        fold_left2_result
          (fun '(rule_log, argvs) arg size =>
          result_bind (interp_rule R Sigma Gamma sched_log rule_log arg) (fun '(rule_log, argv) =>
          result_map (assert_bits argv size) (fun bs =>
          (rule_log, bs :: argvs)))) args argSizes (rule_log, argvs) =
        Success (l, l1) -> log_write_consistent l v.
  Proof.
    induction args; destruct argSizes; cbn in *; inversion 1; intros.
    - t; eassumption.
    - destruct interp_rule as [(?&[ | ?]) | | ] eqn:?; cbn in *.
      + rewrite fold_left2_result_failure in H3; eauto || discriminate.
      + unfold assert_size in *.
        destruct PeanoNat.Nat.eq_dec; cbn in *.
        * inversion H1; subst.
          eapply (IHargs R v Sigma Gamma sched_log l0); eauto.
        * rewrite fold_left2_result_failure in H3; eauto || discriminate.
      + rewrite fold_left2_result_failure in H3; eauto || discriminate.
      + rewrite fold_left2_result_failure in H3; eauto || discriminate.
  Qed.

  Lemma interp_rule_Success_consistent:
    forall r {R v Sigma Gamma} sl rule_log l val,
      env_related (@length bool) v R ->
      log_write_consistent rule_log v ->
      interp_rule R Sigma Gamma sl rule_log r = Success (l, val) ->
      log_write_consistent l v.
    induction r using rule_ind'; cbn; intros; try solve [t; eauto with types].
    - t.
      destruct a, sig; cbn in *.
      eapply interp_rule_Success_call_consistent; eauto.
  Qed.

  Lemma interp_rule_commit_call:
    forall args : list (rule var_t fn_t),
      Forall
        (fun r : rule var_t fn_t =>
           forall (R : env_t REnv) (v : fenv nat nat) (Sigma : env_t SigmaEnv)
             (Gamma : env_t GammaEnv) (sl sl' rule_log l : Log) (val : value),
             env_related (length (A:=bool)) v R ->
             log_write_consistent sl v ->
             log_write_consistent sl' v ->
             interp_rule R Sigma Gamma (sl ++ sl') rule_log r = Success (l, val) ->
             interp_rule (commit_update R sl') Sigma Gamma sl rule_log r = Success (l, val)) args ->
      forall (R : env_t REnv) (Sigma : env_t SigmaEnv) (Gamma : env_t GammaEnv) (sl sl' rule_log l : Log)
             (argSizes : list nat) v argvs,
        length args = length argSizes ->
        env_related (length (A:=bool)) v R ->
        log_write_consistent sl v ->
        log_write_consistent sl' v ->
        forall l1 : list bits,
          fold_left2_result
            (fun '(rule_log, argvs) arg size =>
                result_bind (interp_rule R Sigma Gamma (sl ++ sl') rule_log arg) (fun '(rule_log, argv) =>
                result_map (assert_bits argv size) (fun bs =>
                (rule_log, bs :: argvs)))) args argSizes (rule_log, argvs) =
          Success (l, l1) ->
          fold_left2_result
            (fun '(rule_log, argvs) arg size =>
                result_bind (interp_rule (commit_update R sl') Sigma Gamma sl rule_log arg) (fun '(rule_log, argv) =>
                result_map (assert_bits argv size) (fun bs =>
                (rule_log, bs :: argvs)))) args argSizes (rule_log, argvs) =
          Success (l, l1).
  Proof.
    induction args; destruct argSizes; cbn in *; inversion 1; intros.
    - t. reflexivity.
    - destruct (interp_rule R Sigma Gamma (sl ++ sl') rule_log a) as [(? & ?) | | ] eqn:?; cbn in *.
      + inversion H; subst.
        eapply H8 in Heqr; eauto using log_write_consistent_nil.
        rewrite Heqr; cbn.
        destruct assert_bits; cbn in *.
        * move IHargs at bottom.
          unfold fold_left2_result in *.
          eapply IHargs; eauto.
        * rewrite fold_left2_result_failure in H5; eauto || discriminate.
        * rewrite fold_left2_result_failure in H5; eauto || discriminate.
      + rewrite fold_left2_result_failure in H5; eauto || discriminate.
      + rewrite fold_left2_result_failure in H5; eauto || discriminate.
  Qed.

  Lemma interp_rule_commit:
    forall r {R v Sigma Gamma} sl sl' rule_log l val,
      env_related (@length bool) v R ->
      log_write_consistent sl v ->
      log_write_consistent sl' v ->
      interp_rule R Sigma Gamma (sl ++ sl') rule_log r = Success (l, val) ->
      interp_rule (commit_update R sl') Sigma Gamma sl rule_log r = Success (l, val).
  Proof.
    induction r using rule_ind'; cbn; intros R v Sigma Gamma * Heqiv Hcst Hcst'; intros; try congruence.
    - (* Bind *)
      t. erewrite IHr1; cbn; eauto.
    - (* If *)
      t;
        erewrite IHr1; cbn; eauto;
          [ erewrite IHr2; cbn; eauto |
            erewrite IHr3; cbn; eauto ].
    - destruct port.
      + (* Read0 *)
        t.

        erewrite getenv_commit_update by eassumption.
        destruct latest_write eqn:?; cbn.
        * destruct l; cbn.
          rewrite H1; cbn.
          erewrite may_read0_no_writes in Heqo0; eauto.
          discriminate.

        * rewrite H1; cbn.
          reflexivity.

      + (* Read1 *)
        t;
          rewrite app_assoc in Heqo0;
          rewrite latest_write0_app in Heqo0;
          t;
          erewrite getenv_commit_update by eassumption.
        destruct latest_write eqn:?; cbn.
        * destruct l; cbn.
          rewrite H2; cbn.

          lazymatch goal with
          | [ H: latest_write ?l ?idx = Some ?entry |- _ ] =>
            let v0 := (eval cbn in entry.(Semantics.val)) in
            change v0 with (entry.(Semantics.val));
            erewrite log_write_consistent_latest_write
          end; eauto.
          rewrite assert_size_eq by auto; cbn.
          reflexivity.
        * rewrite H2; cbn.
          rewrite assert_size_eq by auto; cbn.
          reflexivity.
        *

          rewrite may_read1_latest_write_is_0 by eassumption.

          rewrite Heqo0; cbn.
          rewrite H2; cbn.
          reflexivity.

        * rewrite may_read1_latest_write_is_0 by eassumption.
          rewrite Heqo0; cbn.
          rewrite H1; cbn.
          reflexivity.

    - t.
      erewrite getenv_commit_update by eassumption.
      destruct latest_write eqn:?; cbn.
      + destruct l; cbn.
        erewrite IHr by eassumption; cbn.
        rewrite H1; cbn.

          lazymatch goal with
          | [ H: latest_write ?l ?idx = Some ?entry |- _ ] =>
            let v0 := (eval cbn in entry.(Semantics.val)) in
            change v0 with (entry.(Semantics.val));
            erewrite log_write_consistent_latest_write
          end; eauto.
          rewrite assert_size_eq by auto; cbn.

        reflexivity.
      + erewrite IHr by eassumption; cbn.
        rewrite H1; cbn.
        rewrite assert_size_eq by auto; cbn.
        reflexivity.

    - t.
      destruct a, sig; cbn in *.
      erewrite interp_rule_commit_call; cbn; eauto.
  Qed.

  Lemma OneRuleAtATime':
    forall R v Sigma s rs R' l0,
      env_related (@length bool) v R ->
      log_write_consistent l0 v ->
      interp_scheduler_trace_and_update R Sigma l0 s = Some (rs, R') ->
      List.fold_left (update_one Sigma) rs (Some (commit_update R l0)) = Some R'.
  Proof.
    induction s; cbn.
    - inversion 3; subst; cbn in *; eauto.
    - intros * Hequiv Hcst Heq.
      unfold interp_scheduler_trace_and_update in *; cbn in *.
      destruct interp_rule as [(l & ?) | | ] eqn:?; try discriminate.

      + destruct interp_scheduler_trace as [(? & ?) | ] eqn:?; try discriminate;
          inversion Heq; subst; clear Heq; cbn.
        unfold interp_scheduler_trace_and_update; cbn.
        enough (interp_rule (commit_update R l0) Sigma env_nil [] [] r = Success (l, v0)) as H.
        rewrite H.
        rewrite commit_update_assoc.
        rewrite app_nil_r.
        eapply IHs1.
        eassumption.
        apply log_write_consistent_app.
        eassumption.
        eauto using interp_rule_Success_consistent, log_write_consistent_nil.
        rewrite Heqo.
        reflexivity.
        eapply interp_rule_commit.
        eassumption.
        eapply log_write_consistent_nil.
        eassumption.
        rewrite app_nil_l.
        assumption.
      + eapply IHs2.
        eassumption.
        eassumption.
        destruct interp_scheduler_trace as [(? & ?) | ] eqn:?; try discriminate.
        inversion Heq; subst.
        reflexivity.
  Qed.

  Lemma interp_scheduler_trace_correct :
    forall R Sigma s l0 log,
      interp_scheduler R Sigma l0 s = Some log ->
      exists rs, interp_scheduler_trace R Sigma l0 s = Some (rs, log).
  Proof.
    induction s; cbn.
    - inversion 1; subst; eauto.
    - intros * Heq; destruct interp_rule as [(log' & ?) | | ] eqn:?.
      + destruct (IHs1 _ _ Heq) as (rs & Heq').
        rewrite Heq'; eauto.
      + destruct (IHs2 _ _ Heq) as (rs & Heq').
        rewrite Heq'; eauto.
      + discriminate.
  Qed.

  Fixpoint scheduler_rules (s: scheduler) :=
    match s with
    | Done => []
    | Try r s1 s2 => r :: scheduler_rules s1 ++ scheduler_rules s2
    end.

  Lemma scheduler_trace_in_scheduler :
    forall R Sigma s log l0 rs,
      interp_scheduler_trace R Sigma l0 s = Some (rs, log) ->
      (forall r : rule var_t fn_t, In r rs -> In r (scheduler_rules s)).
  Proof.
    induction s; cbn in *.
    - inversion 1; subst; inversion 1.
    - intros * H * H'; rewrite in_app_iff; t.
      + inversion H'; subst; eauto.
      + eauto.
  Qed.

  Theorem OneRuleAtATime:
    forall R Sigma s log,
      interp_scheduler R Sigma [] s = Some log ->
      exists rs,
        (forall r, List.In r rs -> List.In r (scheduler_rules s)) /\
        List.fold_left (update_one Sigma) rs (Some R) = Some (commit_update R log).
  Proof.
    intros * H.
    apply interp_scheduler_trace_correct in H; destruct H as (rs & H).
    exists rs; split.
    - eauto using scheduler_trace_in_scheduler.
    - eapply OneRuleAtATime' with (l0 := nil).
      + eapply tenv_of_env_related.
      + eapply log_write_consistent_nil.
      + unfold interp_scheduler_trace_and_update; rewrite H; reflexivity.
  Qed.
End OneRuleAtATime.