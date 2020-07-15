Require Import Koika.Frontend.
Require Import dynamic_isolation.Interp.
Require Import dynamic_isolation.Tactics.
Require Import Coq.Program.Equality.

Record RLift {T} {A B: Type} {projA: A -> T} {projB: B -> T} := mk_RLift
  { rlift: A -> B
  ; pf_R_equal: forall (a: A), projB (rlift a) = projA a
  ; pf_inj_rlift: forall (a1 a2: A), rlift a1 = rlift a2 -> a1 = a2
  }.
Arguments RLift : clear implicits.

Ltac mk_rlift lift :=
  exists lift; intros;
  repeat match goal with
  | [ H: ?T |- _ ] => is_ind T; destruct H
  end; simpl in *; try congruence; reflexivity.

Ltac mk_rlift_id :=
  exists id; now auto.

Ltac mk_rlift_trivial :=
  exists (fun a : empty_ext_fn_t => match a with end);
    let a := fresh in intros a; destruct a; auto.

Create HintDb lift.

Hint Extern 1 (RLift _ _ _ _ _ ) => mk_rlift_id : lift.
Hint Extern 1 (RLift _ _ _ _ _ ) => mk_rlift_trivial : lift.

Section Inverse.
  Context {A B: Type}.
  Context {FT_A: FiniteType A}.
  Context {EqDec_B: EqDec B}.

  Definition partial_f_inv (f: A -> B) : B -> option A :=
    fun b => List.find (fun a => beq_dec (f a) b) finite_elements.

  Lemma is_partial_f_env (f: A -> B) :
    forall a b,
    partial_f_inv f b = Some a ->
    f a = b.
  Proof.
    unfold partial_f_inv; intros.
    apply find_some in H.
    rewrite beq_dec_iff in H.
    safe_intuition.
  Qed.

End Inverse.

Hint Rewrite @getenv_create : log_helpers.
Hint Rewrite @getenv_map2 : log_helpers.

Section ScheduleLift.
  Context {pos_t : Type} {rule_name_t : Type} {rule_name_t' : Type}.
  Context (lift: rule_name_t -> rule_name_t').

  Fixpoint lift_scheduler (sched: Syntax.scheduler pos_t rule_name_t)
                           : Syntax.scheduler pos_t rule_name_t' :=
    match sched with
    | Done => Done
    | Cons r s => Cons (lift r) (lift_scheduler s)
    | Try r s1 s2 => Try (lift r) (lift_scheduler s1) (lift_scheduler s2)
    | SPos pos s => SPos pos (lift_scheduler s)
    end.

End ScheduleLift.

Section Lift.
  Context {reg_t reg_t' : Type}.
  Context {R: reg_t -> type} {R' : reg_t' -> type}.
  Context {REnv: Env reg_t} {REnv': Env reg_t'}.
  Context (Rlift: RLift type reg_t reg_t' R R').

  Context {FT_reg_t : FiniteType reg_t}.
  Context {EqDec_reg_t : EqDec reg_t}.
  Context {EqDec_reg_t' : EqDec reg_t'}.


  Section LiftEnv.
    Definition proj_env (env': env_t REnv' R') : env_t REnv R.
    Proof.
      refine (REnv.(create) _).
      intro reg. rewrite<-Rlift.(pf_R_equal).
      exact (REnv'.(getenv) env' (Rlift.(rlift) reg)).
    Defined.
  End LiftEnv.

  Section LiftLog.

    Definition lift_log (log: Log R REnv) : Log R' REnv' :=
      create REnv' (fun r' : reg_t' =>
                      match partial_f_inv (rlift Rlift) r' as opt_r
                            return ((partial_f_inv (rlift Rlift) r' = opt_r) -> RLog (R' r')) with
                      | Some r => fun Heq : partial_f_inv (rlift Rlift) r' = Some r =>
                                   let log_r := rew <- [fun t : type => RLog t] pf_R_equal Rlift r in
                                                      getenv REnv log r in
                                   rew [fun r' => RLog (R' r')] (is_partial_f_env (rlift Rlift) r r' Heq) in
                                       log_r
                      | None => fun _ => []
                      end eq_refl).

    Definition proj_log (log' : Log R' REnv') : Log R REnv :=
      create REnv (fun reg : reg_t => rew [fun t : type => RLog t] pf_R_equal Rlift reg in
                                       getenv REnv' log' (Rlift.(rlift) reg)).
  End LiftLog.

  Section Lemmas.
    Lemma getenv_proj_log :
      forall log' r,
      getenv REnv (proj_log log') r =
        rew [fun t : type => RLog t] pf_R_equal Rlift r in
            (getenv REnv' log' (Rlift.(rlift) r)).
    Proof.
      intros.
      unfold proj_log.
      autorewrite with log_helpers.
      auto.
    Qed.

    Lemma getenv_proj_env :
      forall st' r,
      getenv REnv (proj_env st') r =
        (rew <- [fun t : type => t -> R r] pf_R_equal Rlift r in (fun x : R r => x))
          (getenv REnv' st' (rlift Rlift r)).
    Proof.
      intros. unfold proj_env.
      autorewrite with log_helpers.
      elim_eq_rect.
      auto.
    Qed.

    Lemma putenv_proj_log :
      forall log' r rlog,
      putenv REnv (proj_log log') r rlog =
        proj_log
            (putenv REnv' log' (Rlift.(rlift) r) (rew <- [fun t : type => RLog t] pf_R_equal Rlift r in rlog)).
    Proof.
      intros. apply equiv_eq; unfold equiv. intro k.
      destruct EqDec_reg_t.
      destruct (eq_dec r k); subst.
      - rewrite get_put_eq. rewrite getenv_proj_log. rewrite get_put_eq.
        destruct (pf_R_equal Rlift k); simpl; auto.
      - rewrite get_put_neq; auto. rewrite getenv_proj_log.
        rewrite getenv_proj_log. destruct (pf_R_equal Rlift k).
        simpl; auto. rewrite get_put_neq; auto.
        destruct EqDec_reg_t'.
        destruct (eq_dec0 (rlift Rlift r) (rlift Rlift k)); auto.
        apply (pf_inj_rlift Rlift) in e. contradiction.
    Qed.


    Lemma latest_write_proj_log :
      (forall log' r,
         latest_write (proj_log log') r = rew [fun t : type => option t] pf_R_equal Rlift r in
                                              (latest_write log' (Rlift.(rlift) r))).
    Proof.
      intros. unfold proj_log, latest_write, log_find.
      autorewrite with log_helpers.
      elim_eq_rect; simpl; auto.
    Qed.

    Lemma latest_write0_proj_log :
      (forall log' r,
         latest_write0 (proj_log log') r = rew [fun t : type => option t] pf_R_equal Rlift r in
                                               (latest_write0 log' (Rlift.(rlift) r))).
    Proof.
      intros; unfold proj_log, latest_write0, log_find.
      autorewrite with log_helpers.
      elim_eq_rect; simpl; auto.
    Qed.

    Lemma latest_write1_proj_log :
      (forall log' r,
         latest_write1 (proj_log log') r = rew [fun t : type => option t] pf_R_equal Rlift r in
                                               (latest_write1 log' (Rlift.(rlift) r))).
    Proof.
      intros; unfold proj_log, latest_write1, log_find.
      autorewrite with log_helpers.
      elim_eq_rect; simpl; auto.
    Qed.

    Lemma proj_log_empty :
      proj_log log_empty = log_empty.
    Proof.
      apply equiv_eq.
      unfold equiv, proj_log.
      intros.
      unfold log_empty.
      autorewrite with log_helpers.
      elim_eq_rect; simpl; auto.
    Qed.

    Lemma log_app_comm_proj_log :
      forall (log1 log2: Log R' REnv'),
      log_app (R := R) (REnv := REnv) (proj_log log1) (proj_log log2) =
      proj_log (log_app (R := R') log1 log2).
    Proof.
      intros. apply equiv_eq.
      unfold log_app, proj_log, equiv.
      intros.
      autorewrite with log_helpers.
      elim_eq_rect; auto.
    Qed.

    Lemma may_read_proj_eq_may_read_lift :
      forall (log': Log R' REnv') port idx,
      may_read (proj_log log') port idx = may_read (REnv := REnv') log' port (rlift Rlift idx).
    Proof.
      intros; unfold may_read, log_existsb.
      destruct port; repeat rewrite getenv_proj_log; elim_eq_rect; auto.
    Qed.

    Lemma may_write_proj_eq_may_write_lift :
      forall (log1 log2: Log R' REnv') port idx,
      may_write (proj_log log1) (proj_log log2) port idx = may_write (REnv := REnv') log1 log2 port (rlift Rlift idx).
    Proof.
      intros; unfold may_write, log_existsb.
      destruct port; rewrite log_app_comm_proj_log; rewrite getenv_proj_log;
        elim_eq_rect; auto.
    Qed.

  End Lemmas.

End Lift.

Hint Rewrite @Lift.getenv_proj_log : log_helpers.
Hint Rewrite @Lift.putenv_proj_log : log_helpers.
Hint Rewrite @Lift.getenv_proj_env : log_helpers.
Hint Rewrite @Lift.getenv_proj_log : log_helpers.
Hint Rewrite @Lift.latest_write_proj_log : log_helpers.
Hint Rewrite @Lift.latest_write0_proj_log : log_helpers.
Hint Rewrite @Lift.latest_write1_proj_log : log_helpers.
Hint Rewrite @Lift.proj_log_empty : log_helpers.
Hint Rewrite @Lift.log_app_comm_proj_log : log_helpers. (* TODO: make hint work *)
Hint Rewrite @Lift.may_read_proj_eq_may_read_lift : log_helpers. (* TODO: make hint work *)

Section LiftAction.
  Context {reg_t reg_t' : Type}.
  Context {R: reg_t -> type} {R' : reg_t' -> type}.
  Context (Rlift: RLift type reg_t reg_t' R R').

  Context {fn_name_t ext_fn_t ext_fn_t': Type}.

  Context {Sigma: ext_fn_t -> ExternalSignature}.
  Context {Sigma': ext_fn_t' -> ExternalSignature}.
  Context (Fnlift : RLift ExternalSignature ext_fn_t ext_fn_t' Sigma Sigma').

  Notation lift := Rlift.(rlift).

  Section Args.
    Context (lift_action:
               forall {sig: tsig var_t} {ret_ty: type},
                 @TypedSyntax.action pos_t var_t fn_name_t reg_t ext_fn_t R Sigma sig ret_ty ->
                 (@TypedSyntax.action pos_t var_t fn_name_t reg_t' ext_fn_t' R' Sigma' sig ret_ty)).
    Fixpoint lift_args
      {sig: tsig var_t}
      {argspec: tsig var_t}
      (args: context (fun k_tau => @TypedSyntax.action pos_t var_t fn_name_t reg_t ext_fn_t R Sigma sig (snd k_tau))
                     argspec)
      : context (fun k_tau => @TypedSyntax.action pos_t var_t fn_name_t reg_t' ext_fn_t' R' Sigma' sig (snd k_tau)) argspec :=
      (match args with
       | CtxEmpty => CtxEmpty
       | @CtxCons _ _ argspec k_tau arg args =>
         CtxCons k_tau (lift_action _ _ arg) (lift_args args)
       end).
  End Args.

  Fixpoint lift_action {sig: tsig var_t}
                       {ret_ty: type}
                       (action: @TypedSyntax.action pos_t var_t fn_name_t reg_t ext_fn_t R Sigma sig ret_ty)
                       : (@TypedSyntax.action pos_t var_t fn_name_t reg_t' ext_fn_t' R' Sigma' sig ret_ty) :=
    match action in TypedSyntax.action _ _ _ _ _ sig ret_ty
          return TypedSyntax.action _ _ _ _ _ sig ret_ty with
    | Fail tau => Fail tau
    | @Var _ _ _ _ _ _ _ sig k tau m => @Var _ _ _ _ _ _ _ sig k tau m
    | Const cst => Const cst
    | Assign m ex => Assign m (lift_action ex)
    | Seq r1 r2 => Seq (lift_action r1) (lift_action r2)
    | Bind var ex body => Bind var (lift_action ex) (lift_action body)
    | If cond tbranch fbranch => If (lift_action cond)
                                   (lift_action tbranch)
                                   (lift_action fbranch)
    | @Read _ _ _ _ _ _ _ sig0 port idx =>
       rew [fun t : type => TypedSyntax.action pos_t var_t fn_name_t R' Sigma' sig0 t] (Rlift.(pf_R_equal) idx) in
           (Read port (lift idx))
    | @Write _ _ _ _ _ _ _ sig0 port idx value =>
        Write port (lift idx)
              (rew<-[fun t: type => TypedSyntax.action pos_t var_t fn_name_t R' Sigma' sig0 t]
                    (Rlift.(pf_R_equal) idx) in (lift_action value))
    | Unop fn arg1 => Unop fn (lift_action arg1)
    | Binop fn arg1 arg2 => Binop fn (lift_action arg1) (lift_action arg2)
    | @ExternalCall _ _ _ _ _ _ _ sig0 fn arg =>
        rew [fun e : ExternalSignature => TypedSyntax.action pos_t var_t fn_name_t R' Sigma' sig0 (retSig e)]
            pf_R_equal Fnlift fn in
        ExternalCall (rlift Fnlift fn)
          (rew <- [fun t : ExternalSignature => TypedSyntax.action pos_t var_t fn_name_t R' Sigma' sig0 (arg1Sig t)]
               pf_R_equal Fnlift fn in lift_action arg)
    | InternalCall fn args body =>
        InternalCall fn (lift_args (@lift_action) args) (lift_action body)
    | APos pos a => APos pos (lift_action a)
    end.

    Definition lift_rule (rl: @TypedSyntax.rule pos_t var_t fn_name_t reg_t ext_fn_t R Sigma)
                         : @TypedSyntax.rule pos_t var_t fn_name_t reg_t' ext_fn_t' R' Sigma' :=
      lift_action rl.

End LiftAction.

Section Properties_LiftSchedule.
  Context {rule_name_t rule_name_t' reg_t reg_t' ext_fn_t ext_fn_t': Type}.
  Context {R: reg_t -> type} {R' : reg_t' -> type}.
  Context (Rlift: RLift type reg_t reg_t' R R').

  Context {Sigma: ext_fn_t -> ExternalSignature} {Sigma': ext_fn_t' -> ExternalSignature}.
  Context (Fnlift : RLift ExternalSignature ext_fn_t ext_fn_t' Sigma Sigma').
  Context (sigma: forall f, Sig_denote (Sigma f)) (sigma': forall f, Sig_denote (Sigma' f)).

  Context {REnv: Env reg_t} {REnv': Env reg_t'}.
  Context (r: REnv.(env_t) R) (r': REnv'.(env_t) R').

  Context (rule_name_lift: rule_name_t -> rule_name_t').

  Context {FT_reg_t : FiniteType reg_t}.
  Context {EqDec_reg_t : EqDec reg_t}.
  Context {EqDec_reg_t' : EqDec reg_t'}.

  Notation rule' := (rule R' Sigma').
  Notation rule := (rule R Sigma).
  Notation action' := (action R' Sigma').
  Notation action := (action R Sigma).
  Notation schedule' := (scheduler rule_name_t').
  Notation schedule := (scheduler rule_name_t).

  Notation interp_rule := (interp_rule (fn_name_t := fn_name_t)).
  Notation lift_action := (lift_action Rlift Fnlift).
  Notation lift_rule := (lift_rule Rlift Fnlift).
  Notation proj_log := (proj_log (REnv := REnv) Rlift).
  Notation proj_env := (proj_env (REnv := REnv) Rlift).
  Context (rules: rule_name_t -> rule) (rules': rule_name_t' -> rule').

  Definition proj_interp_action_result {sig: tsig var_t} {ret_ty: type}
                                (res': option (Log R' REnv' * ret_ty * (tcontext sig)))
                                : option (Log R REnv * ret_ty * (tcontext sig)) :=
    match res' with
    | None => None
    | Some (v1, v2, v3) => Some (proj_log v1, v2, v3)
    end.

  Section LiftActionPreserves.

    Ltac _start := simpl; unfold opt_bind, proj_interp_action_result in *; intros; auto.
    Ltac _destruct := match_innermost_in_goal; destruct_pairs; auto.

    Fixpoint lift_action_preserves {sig: tsig var_t}
                                   {ret_ty : type}
                                   (action: action sig ret_ty)
                                   {struct action}:
      forall
        (st': REnv'.(env_t) (fun idx: reg_t' => R' idx))
        (sched_log: Log R' REnv') (action_log: Log R' REnv') (gamma: tcontext sig),
      (forall f, Sigma f = Sigma' (Fnlift.(rlift) f)) ->
      (forall f, sigma f = rew [fun e : ExternalSignature => Sig_denote e] pf_R_equal Fnlift f in sigma' (Fnlift.(rlift) f)) ->
      interp_action (proj_env st') sigma gamma (proj_log sched_log) (proj_log action_log) action =
      proj_interp_action_result (interp_action st' sigma' gamma sched_log action_log (lift_action action)).

    Proof.
      * destruct action.
        (* Fail *)
        - _start.
        (* Var *)
        - _start.
        (* Const *)
        - _start.
        (* Assign *)
        - _start.
          rewrite lift_action_preserves; auto.
          _destruct.
        (* Seq *)
        - _start.
          rewrite lift_action_preserves; auto.
          _destruct.
        (* Bind *)
        - _start.
          rewrite lift_action_preserves; auto.
          _destruct.
          rewrite lift_action_preserves; auto.
          _destruct.
        (* If *)
        - _start.
          rewrite lift_action_preserves; auto.
          _destruct.
          _destruct.
        (* Read *)
        - _start.
          destruct port; simpl.
          + _destruct.
            { unfold log_cons.
              autorewrite with log_helpers.
              rewrite putenv_proj_log; auto.
              elim_eq_rect; simpl; auto.
              rewrite may_read_proj_eq_may_read_lift in Heqb.
              simpl_match; auto.
            }
            { elim_eq_rect; simpl.
              rewrite may_read_proj_eq_may_read_lift in Heqb.
              simpl_match; auto.
            }
          + _destruct.
             { unfold log_cons.
               autorewrite with log_helpers.
               rewrite putenv_proj_log; auto.
               rewrite log_app_comm_proj_log.
               autorewrite with log_helpers.
               elim_eq_rect; simpl; auto.
               rewrite may_read_proj_eq_may_read_lift in Heqb.
               simpl_match; auto.
             }
             { elim_eq_rect; simpl; auto.
               rewrite may_read_proj_eq_may_read_lift in Heqb.
               simpl_match; auto.
             }
        (* Write *)
        - _start.
          rewrite lift_action_preserves; auto.
          unfold eq_rect_r.
          _destruct.
          { _destruct.
            { unfold log_cons.
              autorewrite with log_helpers.
              rewrite putenv_proj_log; auto.
              unfold eq_rect_r; destruct (pf_R_equal Rlift idx); simpl_eqs; simpl in *;
                option_simpl; simplify_tuples; subst.
              rewrite may_write_proj_eq_may_write_lift in Heqb.
              rewrite Heqo. simpl_match. auto.
            }
            { destruct (pf_R_equal Rlift idx); simpl_eqs.
              simpl_match.
              rewrite may_write_proj_eq_may_write_lift in Heqb.
              simpl_match; auto.
            }
          }
          { destruct (pf_R_equal Rlift idx); simpl_eqs.
            simpl_match; auto.
          }
        (* Unop *)
        - _start.
          rewrite lift_action_preserves; auto.
          _destruct.
        (* Binop *)
        - _start.
          rewrite lift_action_preserves; auto.
          _destruct.
          rewrite lift_action_preserves; auto.
          _destruct.
        (* ExternalCall *)
        - _start.
          rewrite lift_action_preserves; auto.
          unfold eq_rect_r in *.
          _destruct.
          { rewrite H0. destruct (pf_R_equal Fnlift fn); simpl in *.
            rewrite Heqo. auto.
          }
          { destruct (pf_R_equal Fnlift fn); simpl.
            rewrite Heqo; auto.
          }
        (* InternalCall *)
        - _start.
          (* TODO: Can we do this with a lemma ... with ... ? *)
          assert (
           forall (sig argspec: tsig var_t) (args: acontext sig argspec)
           (st': env_t REnv' R') gamma sched_log action_log,
           (forall f, Sigma f = Sigma' (Fnlift.(rlift) f)) ->
           (forall f, sigma f = rew [fun e : ExternalSignature => Sig_denote e] pf_R_equal Fnlift f in sigma' (Fnlift.(rlift) f)) ->
           match interp_args (proj_env st') sigma gamma (proj_log sched_log) (proj_log action_log) args with
           | Some (action_log0, results, Gamma) =>
               exists log', interp_args st' sigma' gamma sched_log action_log
                 (lift_args (@Lift.lift_action reg_t reg_t' R R' Rlift fn_name_t ext_fn_t ext_fn_t' Sigma Sigma' Fnlift)
                    args) = Some (log', results, Gamma) /\
                 action_log0 = proj_log log'
           | None => interp_args st' sigma' gamma sched_log action_log
                 (lift_args (sig := sig) (@Lift.lift_action reg_t reg_t' R R' Rlift fn_name_t ext_fn_t ext_fn_t' Sigma Sigma' Fnlift)
                    args) = None
           end) as lift_args_preserves.
          { clear - lift_action_preserves.
            induction args.
            + simpl; intros; auto.
              exists action_log; auto.
            + intros; simpl. unfold opt_bind.
              specialize IHargs with (st' := st') (gamma := gamma)
                                                  (sched_log := sched_log) (action_log := action_log).
              intuition.
              _destruct; propositional.
              { specialize lift_action_preserves with (action := v) (gamma := p1) (st' := st')
                                                      (sched_log := sched_log) (action_log := log').
                rewrite lift_action_preserves; auto.
                unfold proj_interp_action_result.
                simpl_match.
                _destruct.
                eexists; eauto.
              }
              { simpl_match. auto. }
          }
          { specialize lift_args_preserves with (st' := st') (gamma := gamma)
                                              (sched_log := sched_log) (action_log := action_log) (args := args).
            _destruct; propositional; simpl_match; auto.
            rewrite lift_action_preserves; auto.
            _destruct.
          }
        - _start.
    Qed.

  End LiftActionPreserves.

  Lemma interp_rule_comm_proj :
    forall rule (log_input: Log R' REnv'),
    (forall f, Sigma f = Sigma' (Fnlift.(rlift) f)) ->
    (forall f, sigma f = rew [fun e : ExternalSignature => Sig_denote e] pf_R_equal Fnlift f in sigma' (Fnlift.(rlift) f)) ->
    match interp_rule (proj_env r') sigma (proj_log log_input) rule with
    | Some l => exists l', interp_rule r' sigma' log_input (lift_rule rule) = Some l' /\
                     proj_log l' = l
    | None => interp_rule r' sigma' log_input (lift_rule rule) = None
    end.
  Proof.
    unfold interp_rule.
    intros.
    rewrite<-@proj_log_empty with (Rlift := Rlift) (REnv' := REnv').
    rewrite lift_action_preserves; auto.
    unfold proj_interp_action_result.
    fast_match_innermost_in_goal; auto.
    - destruct_pairs. unfold lift_rule.
      simpl_match. eexists; eauto.
    - unfold lift_rule. simpl_match. reflexivity.
  Qed.

  Lemma interp_scheduler_delta'_comm_proj :
    forall schedule (log_input acc_log: Log R' REnv'),
    (forall rule, rules' (rule_name_lift rule) = lift_rule (rules rule)) ->
    (forall f, Sigma f = Sigma' (Fnlift.(rlift) f)) ->
    (forall f, sigma f = rew [fun e : ExternalSignature => Sig_denote e] pf_R_equal Fnlift f in sigma' (Fnlift.(rlift) f)) ->
    interp_scheduler_delta' (REnv := REnv) (proj_env r') sigma rules
                            (proj_log log_input) (proj_log acc_log) schedule =
    proj_log (interp_scheduler_delta' r' sigma' rules' log_input acc_log (lift_scheduler rule_name_lift schedule)).
  Proof.
    induction schedule; simpl; intros; auto.
    - intros. rewrite log_app_comm_proj_log.
      pose proof interp_rule_comm_proj as Hrule.
      match_innermost_in_goal;
        specialize Hrule with (rule := rules r0) (log_input := log_app acc_log log_input);
        rewrite Heqo in Hrule; intuition;
        rewrite H; simpl_match.
      + rewrite log_app_comm_proj_log; auto.
      + auto.
    - intros. rewrite log_app_comm_proj_log.
      pose proof interp_rule_comm_proj as Hrule.
      match_innermost_in_goal;
        specialize Hrule with (rule := rules r0) (log_input := log_app acc_log log_input);
        rewrite Heqo in Hrule; intuition;
        rewrite H; simpl_match.
      + rewrite log_app_comm_proj_log; auto.
      + auto.
  Qed.

  Lemma interp_scheduler_delta_comm_proj :
    forall schedule (log_input: Log R' REnv'),
    (forall rule, rules' (rule_name_lift rule) = lift_rule (rules rule)) ->
    (forall f, Sigma f = Sigma' (Fnlift.(rlift) f)) ->
    (forall f, sigma f = rew [fun e : ExternalSignature => Sig_denote e] pf_R_equal Fnlift f in sigma' (Fnlift.(rlift) f)) ->
    interp_scheduler_delta (REnv := REnv) (proj_env r') sigma rules (proj_log log_input) schedule =
    proj_log
      (interp_scheduler_delta r' sigma' rules' log_input (lift_scheduler rule_name_lift schedule)).
  Proof.
    unfold interp_scheduler_delta.
    intros.
    rewrite<-interp_scheduler_delta'_comm_proj; auto.
    autorewrite with log_helpers; reflexivity.
  Qed.

  (* TODO: rename *)
  Lemma log_app_interp_schedulre_delta_proj_comm_proj_interp_scheduler' :
    forall schedule (log_input: Log R' REnv'),
    (forall rule, rules' (rule_name_lift rule) = lift_rule (rules rule)) ->
    (forall f, Sigma f = Sigma' (Fnlift.(rlift) f)) ->
    (forall f, sigma f = rew [fun e : ExternalSignature => Sig_denote e] pf_R_equal Fnlift f in sigma' (Fnlift.(rlift) f)) ->
    log_app (interp_scheduler_delta (proj_env r') sigma rules (proj_log log_input) schedule) (proj_log log_input) =
    proj_log (interp_scheduler' r' sigma' rules' log_input (lift_scheduler rule_name_lift schedule)).
  Proof.
    intros.
    rewrite interp_scheduler_delta_correspond_to_interp_scheduler.
    rewrite interp_scheduler_delta_comm_proj; auto.
    rewrite log_app_comm_proj_log. auto.
  Qed.

End Properties_LiftSchedule.

Ltac lift_auto := auto with lift.

