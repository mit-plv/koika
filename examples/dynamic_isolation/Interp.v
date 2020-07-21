Require Import Koika.Common.
Require Import Koika.Environments.
Require Import Koika.Logs.
Require Import Koika.Syntax.
Require Import Koika.TypedSemantics.
Require Import Koika.TypedSyntax.

Require Import dynamic_isolation.Tactics.


Section Interp.
  Context {pos_t var_t fn_name_t rule_name_t reg_t ext_fn_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.

  Context {R: reg_t -> type}.
  Context {Sigma: ext_fn_t -> ExternalSignature}.

  Context {REnv: Env reg_t}.
  Context (r: REnv.(env_t) R).
  Context (sigma: forall f, Sig_denote (Sigma f)).

  Notation Log := (Log R REnv).

  Notation rule := (rule pos_t var_t fn_name_t R Sigma).
  Notation action := (action pos_t var_t fn_name_t R Sigma).
  Notation scheduler := (scheduler pos_t rule_name_t).
  Notation interp_rule := (interp_rule r sigma).

  Fixpoint schedule_app (sched1: scheduler) (sched2: scheduler) : scheduler :=
    match sched1 with
    | Done => sched2
    | Cons r s => Cons r (schedule_app s sched2)
    | Try r s1 s2 => Try r (schedule_app s1 sched2) (schedule_app s2 sched2)
    | SPos v s => SPos (rule_name_t := rule_name_t) v (schedule_app s sched2)
    end.

  Section Scheduler.
    Context (rules: rule_name_t -> rule).

    Fixpoint interp_scheduler_delta'
             (sched_log: Log)
             (acc_log: Log)
             (s: scheduler)
             {struct s} :=
      let interp_try r s1 s2 :=
          match interp_rule (log_app acc_log sched_log) (rules r) with
          | Some l => interp_scheduler_delta' sched_log (log_app l acc_log) s1
          | None => interp_scheduler_delta' sched_log acc_log s2
          end in
      match s with
      | Done => acc_log
      | Cons r s => interp_try r s s
      | Try r s1 s2 => interp_try r s1 s2
      | SPos _ s => interp_scheduler_delta' sched_log acc_log s
      end.

    Definition interp_scheduler_delta (sched_log: Log) (s: scheduler) :=
      interp_scheduler_delta' sched_log log_empty s.

  End Scheduler.

  Section Lemmas.
    Context (rules: rule_name_t -> rule).

    Notation interp_scheduler' := (interp_scheduler' r sigma rules).
    Notation interp_scheduler_delta' := (interp_scheduler_delta' rules).
    Notation interp_scheduler_delta := (interp_scheduler_delta rules).

    Lemma interp_scheduler'_app :
      forall (sched1 sched2: scheduler) (log: Log),
      interp_scheduler' log (schedule_app sched1 sched2) =
        interp_scheduler' (interp_scheduler' log sched1) sched2.
    Proof.
      induction sched1; auto.
      - intros; simpl.
        repeat rewrite IHsched1.
        destruct_goal_matches.
      - intros; simpl.
        repeat rewrite IHsched1_1.
        repeat rewrite IHsched1_2.
        destruct_goal_matches; auto.
    Qed.

    Hint Rewrite @SemanticProperties.log_app_assoc : log_rewrites.
    Hint Rewrite @SemanticProperties.log_app_empty_r : log_rewrites.


    Lemma interp_scheduler'_delta_log_app :
      forall sched l1 l2 l3,
      interp_scheduler_delta' l2 (log_app l3 l1) sched =
      log_app (interp_scheduler_delta' (log_app l1 l2) l3 sched) l1.
    Proof.
      induction sched; auto.
      - intros; simpl.
        autorewrite with log_rewrites; destruct_goal_matches.
        autorewrite with log_rewrites; auto.
      - intros; simpl.
        autorewrite with log_rewrites; destruct_goal_matches.
        autorewrite with log_rewrites; auto.
    Qed.

    Lemma interp_scheduler_delta'_correspond_to_interp_scheduler' :
      forall (sched: scheduler) (sched_log: Log) (acc_log: Log),
      interp_scheduler' (log_app acc_log sched_log) sched =
        log_app (interp_scheduler_delta' sched_log acc_log sched) sched_log.
    Proof.
      induction sched; auto.
      - intros; simpl.
        destruct_goal_matches.
        repeat rewrite IHsched.
        rewrite interp_scheduler'_delta_log_app.
        autorewrite with log_rewrites; auto.
      - intros; simpl.
        destruct_goal_matches.
        repeat rewrite IHsched1.
        rewrite interp_scheduler'_delta_log_app.
        autorewrite with log_rewrites; auto.
     Qed.

    Lemma interp_scheduler_delta_correspond_to_interp_scheduler :
      forall (sched: scheduler) (sched_log: Log) ,
      interp_scheduler' sched_log sched =
        log_app (interp_scheduler_delta sched_log sched) sched_log.
    Proof.
      intros. unfold interp_scheduler_delta.
      rewrite<-interp_scheduler_delta'_correspond_to_interp_scheduler'.
      autorewrite with log_rewrites. auto.
    Qed.

    Lemma interp_scheduler_delta_correspond_to_interp_scheduler_empty :
      forall (sched: scheduler)  ,
      interp_scheduler' log_empty sched =
        interp_scheduler_delta log_empty sched.
    Proof.
      intros. rewrite interp_scheduler_delta_correspond_to_interp_scheduler.
      rewrite SemanticProperties.log_app_empty_l.
      auto.
    Qed.

  End Lemmas.
End Interp.

Section Lemmas_InterpScheduler.
  Context {pos_t var_t fn_name_t reg_t ext_fn_t: Type}.
  Context {R: reg_t -> type}.
  Context {Sigma: ext_fn_t -> ExternalSignature}.

  Context {REnv: Env reg_t}.
  Context (r: REnv.(env_t) R).
  Context (sigma: forall f, Sig_denote (Sigma f)).

  Notation interp_scheduler' := (interp_scheduler' r sigma).
  Notation interp_scheduler_delta := (interp_scheduler_delta r sigma).
  Notation interp_scheduler_delta' := (interp_scheduler_delta' r sigma).

  Notation rule := (rule pos_t var_t fn_name_t R Sigma).

  Fixpoint equivalent_rules {rule_name_t rule_name_t' : Type}
                            (rules1: rule_name_t -> rule) (sched1: scheduler pos_t rule_name_t)
                            (rules2: rule_name_t' -> rule) (sched2: scheduler pos_t rule_name_t') : Prop :=
    match sched1, sched2 with
    | Done, Done => True
    | Cons r1 s1, Cons r2 s2 =>
       rules1 r1 = rules2 r2 /\
       equivalent_rules rules1 s1 rules2 s2
    | Try r1 s1 s1', Try r2 s2 s2' =>
        rules1 r1 = rules2 r2 /\
        equivalent_rules rules1 s1 rules2 s2 /\
        equivalent_rules rules1 s1' rules2 s2'
    | SPos v1 s1, SPos v2 s2 =>
        v1 = v2 /\
        equivalent_rules rules1 s1 rules2 s2
    | _, _ => False
    end.

  Lemma interp_scheduler'_rules_equiv :
    forall {rule_name_t rule_name_t'}
      (rules1: rule_name_t -> rule) (sched1: scheduler pos_t rule_name_t)
      (rules2: rule_name_t' -> rule) (sched2: scheduler pos_t rule_name_t') log_input,
    equivalent_rules rules1 sched1 rules2 sched2 ->
    interp_scheduler' rules1 log_input sched1 =
    interp_scheduler' rules2 log_input sched2.
  Proof.
    induction sched1; induction sched2; simpl; auto.
    - intros; propositional.
      rewrite H0.
      match_innermost_in_goal; auto.
    - intros; propositional.
      rewrite H0.
      match_innermost_in_goal; auto.
    - intros; propositional.
  Qed.

  Lemma interp_scheduler_delta'_rules_equiv :
    forall {rule_name_t rule_name_t'}
      (rules1: rule_name_t -> rule) (sched1: @Syntax.scheduler pos_t rule_name_t)
      (rules2: rule_name_t' -> rule) (sched2: @Syntax.scheduler pos_t rule_name_t')
      sched_log acc_log,
    equivalent_rules rules1 sched1 rules2 sched2 ->
    interp_scheduler_delta' rules1 sched_log acc_log sched1 =
    interp_scheduler_delta' rules2 sched_log acc_log sched2.
  Proof.
    induction sched1; induction sched2; simpl; auto.
    - intros; propositional.
      rewrite H0.
      match_innermost_in_goal; auto.
    - intros; propositional.
      rewrite H0.
      match_innermost_in_goal; auto.
    - intros; propositional.
  Qed.

  Lemma interp_scheduler_delta_rules_equiv :
    forall (sched_log: Log R REnv) {rule_name_t rule_name_t'}
      (rules1: rule_name_t -> rule) (sched1: @Syntax.scheduler pos_t rule_name_t)
      (rules2: rule_name_t' -> rule) (sched2: @Syntax.scheduler pos_t rule_name_t'),
    equivalent_rules rules1 sched1 rules2 sched2 ->
    interp_scheduler_delta rules1 sched_log sched1 =
    interp_scheduler_delta rules2 sched_log sched2.
  Proof.
    unfold interp_scheduler_delta.
    intros.
    apply interp_scheduler_delta'_rules_equiv; auto.
  Qed.

End Lemmas_InterpScheduler.

Notation "r '||>' s" :=
  (schedule_app r s)
    (at level 99, s at level 99, right associativity).
