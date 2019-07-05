Require Import SGA.Common SGA.Syntax SGA.Semantics.

Require Import List.
Import ListNotations.

Open Scope bool_scope.

Definition rule_ind' {TVar TFn : Type} (P : rule TVar TFn -> Prop)
           (f : forall (var : TVar) (expr : rule TVar TFn),
               P expr -> forall body : rule TVar TFn, P body -> P (Bind var expr body))
           (f0 : forall var : TVar, P (Var var)) (f1 : P Skip) (f2 : forall cst : bits, P (Const cst))
           (f3 : forall cond : rule TVar TFn,
               P cond ->
               forall tbranch : rule TVar TFn,
                 P tbranch -> forall fbranch : rule TVar TFn, P fbranch -> P (If cond tbranch fbranch))
           (f4 : P Fail) (f5 : forall (level : Level) (idx : nat), P (Read level idx))
           (f6 : forall (level : Level) (idx : nat) (value : rule TVar TFn), P value -> P (Write level idx value))
           (f7: forall (fn : TFn) (args : list (rule TVar TFn)),
               List.Forall P args ->
               P (Call fn args)) : forall r, P r.
  refine (fix F (r : rule TVar TFn) : P r :=
    match r as r0 return (P r0) with
    | Bind var expr body => f var expr (F expr) body (F body)
    | Var var => f0 var
    | Skip => f1
    | Const cst => f2 cst
    | If cond tbranch fbranch => f3 cond (F cond) tbranch (F tbranch) fbranch (F fbranch)
    | Fail => f4
    | Read level idx => f5 level idx
    | Write level idx value => f6 level idx value (F value)
    | Call fn args => f7 fn args _
    end).
  revert args.
  fix fargs 1.
  destruct args; cbn; econstructor; eauto.
Defined.

Section EnvUpdates.
  Context {RegEnv: Env nat bits}.

  Definition commit_update V0 log : RegEnv.(env_t) :=
    List.fold_right (fun entry V => match entry with
                                  | LE LogWrite _ r bs => putenv V r bs
                                  | _ => V
                                  end)
                    V0 log.

  Lemma commit_update_assoc:
    forall (V : RegEnv.(env_t)) (l l' : Log),
      commit_update (commit_update V l) l' = commit_update V (l' ++ l).
  Proof.
    unfold commit_update; intros; rewrite fold_right_app; reflexivity.
  Qed.

  Section Semantics'.
    Context {TVar: Type}.
    Context {TFn: Type}.

    Context {SigmaEnv: Env TFn ExternalFunction}.
    Context {GammaEnv: Env TVar value}.

    Fixpoint interp_scheduler
          (V: RegEnv.(env_t))
          (Sigma: SigmaEnv.(env_t))
          (sched_log: Log)
          (s: scheduler TVar TFn)
          {struct s} :=
    match s with
    | Done => Some ([], sched_log)
    | Try r s1 s2 =>
      match interp_rule V Sigma env_nil sched_log [] r with
      | Success (l, _) => match interp_scheduler V Sigma (l ++ sched_log) s1 with
                         | Some (rs, log) => Some (r :: rs, log)
                         | None => None
                         end
      | CannotRun => interp_scheduler V Sigma sched_log s2
      | Stuck => None
      end
    end.

    Definition interp_scheduler_and_update
          (V: RegEnv.(env_t))
          (Sigma: SigmaEnv.(env_t))
          (s: scheduler TVar TFn)
          l :=
      match interp_scheduler V Sigma l s with
      | Some (rs, log) => Some (rs, commit_update V log)
      | None => None
      end.

    Definition update_one Sigma V r :=
      match V with
      | None => None
      | Some V => match interp_scheduler_and_update V Sigma (Try r Done Done) [] with
                 | Some (_, V') => Some V'
                 | None => None
                 end
      end.

    Definition latest_write l idx :=
      log_find l idx (fun kind _ _ => match kind with
                                   | LogWrite => true
                                   | _ => false
                                   end).

    Lemma getenv_commit_update :
      forall sl V idx val,
        getenv V idx = Some val ->
        getenv (commit_update V sl) idx =
        match latest_write sl idx with
        | Some {| val := val' |} => Some val'
        | None => Some val
        end.
    Proof.
      induction sl; cbn; intros.
      - assumption.
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
      forall l l' reg (f: LogEntryKind -> Level -> bits -> bool),
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
        List.In e l /\ e.(reg) = idx /\ P e.(kind) e.(level) e.(val) = true.
    Proof.
      unfold log_find; intros * H; destruct e; apply find_some in H.
      destruct (PeanoNat.Nat.eq_dec idx reg); subst; cbn in *.
      - intuition eauto.
      - intuition discriminate.
    Qed.

    Ltac bool_step :=
      match goal with
      | [ H: _ && _ = true |- _ ] =>
        apply andb_prop in H
      | [ H: forallb _ (_ ++ _) = _ |- _ ] =>
        rewrite forallb_app in H
      | [ H: log_forallb (_ ++ _) _ _ = _ |- _ ] =>
        rewrite log_forallb_app in H
      | [ H: Some _ = Some _ |- _ ] =>
        inversion H; subst; clear H
      end.

    Ltac cleanup_step :=
      match goal with
      | _ => discriminate
      | _ => progress (subst; cbn)
      | [ H: Some _ = Some _ |- _ ] =>
        inversion H; subst; clear H
      | [ H: (_, _) = (_, _) |- _ ] =>
        inversion H; subst; clear H
      | [ H: _ /\ _ |- _ ] =>
        destruct H
      end.

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
      destruct level; discriminate.
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
        destruct level; cbn in *; try discriminate; reflexivity.
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
      forall l (v: Typechecking.fenv nat nat) idx e n,
        log_write_consistent l v ->
        Typechecking.fn v idx n ->
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
      | [ H: env_equiv (Env := ?Env) ?f ?tenv ?env,
             H': getenv ?env ?k = Some ?v |- _ ] =>
        pose_once (and_fst H k v) H'
      | [ H: env_equiv ?f ?tenv ?env,
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
      forall (args : list (rule TVar TFn)) (V : env_t RegEnv) (v : Typechecking.fenv nat nat)
        (Sigma : env_t SigmaEnv) (Gamma : env_t GammaEnv) (sched_log rule_log l : Log) argvs,
        env_equiv (length (A:=bool)) v V ->
        log_write_consistent rule_log v ->
        Forall
          (fun r : rule TVar TFn =>
             forall (V : env_t RegEnv) (v : Typechecking.fenv nat nat) (Sigma : env_t SigmaEnv)
               (Gamma : env_t GammaEnv) (sl rule_log l : Log) (val : value),
               env_equiv (length (A:=bool)) v V ->
               log_write_consistent rule_log v ->
               interp_rule V Sigma Gamma sl rule_log r = Success (l, val) -> log_write_consistent l v) args ->
        forall (l1 : list bits) (argSizes : list nat),
          length args = length argSizes ->
          fold_left2_result
            (fun '(rule_log, argvs) arg size =>
            result_bind (interp_rule V Sigma Gamma sched_log rule_log arg) (fun '(rule_log, argv) =>
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
            eapply (IHargs V v Sigma Gamma sched_log l0); eauto.
          * rewrite fold_left2_result_failure in H3; eauto || discriminate.
        + rewrite fold_left2_result_failure in H3; eauto || discriminate.
        + rewrite fold_left2_result_failure in H3; eauto || discriminate.
    Qed.

    Lemma interp_rule_Success_consistent:
      forall r {V v Sigma Gamma} sl rule_log l val,
        env_equiv (@length bool) v V ->
        log_write_consistent rule_log v ->
        interp_rule V Sigma Gamma sl rule_log r = Success (l, val) ->
        log_write_consistent l v.
      induction r using rule_ind'; cbn; intros; try solve [t; eauto with types].
      - t.
        destruct a, sig; cbn in *.
        eapply interp_rule_Success_call_consistent; eauto.
    Qed.

    Lemma interp_rule_commit_call:
      forall args : list (rule TVar TFn),
        Forall
          (fun r : rule TVar TFn =>
             forall (V : env_t RegEnv) (v : Typechecking.fenv nat nat) (Sigma : env_t SigmaEnv)
               (Gamma : env_t GammaEnv) (sl sl' rule_log l : Log) (val : value),
               env_equiv (length (A:=bool)) v V ->
               log_write_consistent sl v ->
               log_write_consistent sl' v ->
               interp_rule V Sigma Gamma (sl ++ sl') rule_log r = Success (l, val) ->
               interp_rule (commit_update V sl') Sigma Gamma sl rule_log r = Success (l, val)) args ->
        forall (V : env_t RegEnv) (Sigma : env_t SigmaEnv) (Gamma : env_t GammaEnv) (sl sl' rule_log l : Log)
               (argSizes : list nat) v argvs,
          length args = length argSizes ->
          env_equiv (length (A:=bool)) v V ->
          log_write_consistent sl v ->
          log_write_consistent sl' v ->
          forall l1 : list bits,
            fold_left2_result
              (fun '(rule_log, argvs) arg size =>
                  result_bind (interp_rule V Sigma Gamma (sl ++ sl') rule_log arg) (fun '(rule_log, argv) =>
                  result_map (assert_bits argv size) (fun bs =>
                  (rule_log, bs :: argvs)))) args argSizes (rule_log, argvs) =
            Success (l, l1) ->
            fold_left2_result
              (fun '(rule_log, argvs) arg size =>
                  result_bind (interp_rule (commit_update V sl') Sigma Gamma sl rule_log arg) (fun '(rule_log, argv) =>
                  result_map (assert_bits argv size) (fun bs =>
                  (rule_log, bs :: argvs)))) args argSizes (rule_log, argvs) =
            Success (l, l1).
    Proof.
      induction args; destruct argSizes; cbn in *; inversion 1; intros.
      - t. reflexivity.
      - destruct (interp_rule V Sigma Gamma (sl ++ sl') rule_log a) as [(? & ?) | | ] eqn:?; cbn in *.
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
      forall r {V v Sigma Gamma} sl sl' rule_log l val,
        env_equiv (@length bool) v V ->
        log_write_consistent sl v ->
        log_write_consistent sl' v ->
        interp_rule V Sigma Gamma (sl ++ sl') rule_log r = Success (l, val) ->
        interp_rule (commit_update V sl') Sigma Gamma sl rule_log r = Success (l, val).
    Proof.
      induction r using rule_ind'; cbn; intros V v Sigma Gamma * Heqiv Hcst Hcst'; intros; try congruence.
      - (* Bind *)
        t. erewrite IHr1; cbn; eauto.
      - (* If *)
        t;
          erewrite IHr1; cbn; eauto;
            [ erewrite IHr2; cbn; eauto |
              erewrite IHr3; cbn; eauto ].
      - destruct level.
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

  Lemma OneRuleAtATime:
    forall Sigma s V v rs V' l0,
      env_equiv (@length bool) v V ->
      log_write_consistent l0 v ->
      interp_scheduler_and_update V Sigma s l0 = Some (rs, V') ->
      List.fold_left (update_one Sigma) rs (Some (commit_update V l0)) = Some V'.
  Proof.
    induction s; cbn.
    - inversion 3; subst; cbn in *; eauto.
    - intros * Hequiv Hcst Heq.
      unfold interp_scheduler_and_update in *; cbn in *.
      destruct interp_rule as [(l & ?) | | ] eqn:?; try discriminate.

      + destruct interp_scheduler as [(? & ?) | ] eqn:?; try discriminate;
          inversion Heq; subst; clear Heq; cbn.
        unfold interp_scheduler_and_update; cbn.
        enough (interp_rule (commit_update V l0) Sigma env_nil [] [] r = Success (l, v0)) as H.
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
        destruct interp_scheduler as [(? & ?) | ] eqn:?; try discriminate.
        inversion Heq; subst.
        reflexivity.
  Qed.
  End Semantics'.