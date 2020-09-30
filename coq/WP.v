Require Import CompactSemantics.
Require Import Magic.

Section CPS.
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

  Definition tcontext (sig: tsig var_t) :=
    context (fun k_tau => type_denote (snd k_tau)) sig.

  Definition acontext (sig argspec: tsig var_t) :=
    context (fun k_tau => action sig (snd k_tau)) argspec.

  (* Cool trick: generalizing the return types simplifies the correctness proof a lot *)
  Definition action_continuation A sig tau := option (Log * tau * (tcontext sig)) -> A.
  Definition rule_continuation A := option Log -> A.
  Definition scheduler_continuation A := Log -> A.
  Definition cycle_continuation A := REnv.(env_t) R -> A.

  (* FIXME what's the right terminology for interpreter? *)
  Definition action_interpreter A sig := forall (Gamma: tcontext sig) (action_log: Log), A.
  Definition interpreter A := forall (log: Log), A.

  (* Definition wp_bind (p: Log * tau * (tcontext sig) -> Prop) p' := *)
  (*   fun res => *)
  (*     match res with *)
  (*     | Some res => p res *)
  (*     | None => p None *)
  (*     end *)

  (* FIXME monad *)

  Section Action.
    Fixpoint interp_action_cps {sig tau} {A} (L: Log) (a: action sig tau) (k: action_continuation A sig tau) : action_interpreter A sig :=
      let cps {sig tau} a k := @interp_action_cps sig tau A L a k in
      match a in TypedSyntax.action _ _ _ _ _ ts tau return (action_continuation A ts tau -> action_interpreter A ts)  with
      | Fail tau => fun k Gamma l => k None
      | Var m => fun k Gamma l => k (Some (l, cassoc m Gamma, Gamma))
      | Const cst => fun k Gamma l => k (Some (l, cst, Gamma))
      | Seq r1 r2 =>
        fun k =>
          cps r1 (fun res =>
                    match res with
                    | Some (l, v, Gamma) => cps r2 k Gamma l
                    | None => k None
                    end)
      | Assign m ex =>
        fun k =>
          cps ex (fun res =>
                    match res with
                    | Some (l, v, Gamma) => k (Some (l, Ob, creplace m v Gamma))
                    | None => k None
                    end)
      | Bind var ex body =>
        fun k =>
          cps ex (fun res =>
                    match res with
                    | Some (l, v, Gamma) =>
                      cps body (fun res =>
                                  match res with
                                  | Some (l, v, Gamma) =>
                                    k (Some (l, v, ctl Gamma))
                                  | None =>
                                    k None
                                  end) (CtxCons (var, _) v Gamma) l
                    | None => k None
                    end)
      | If cond tbranch fbranch =>
        fun k =>
          cps cond (fun res =>
                      match res with
                      | Some (l, v, Gamma) =>
                        if Bits.single v then cps tbranch k Gamma l
                        else cps fbranch k Gamma l
                      | None => k None
                      end)
      | Read P0 idx =>
        fun k Gamma l =>
          if may_read0 L idx then
            k (Some (Environments.update
                       REnv l idx
                       (fun rl => {| lread0 := true; lread1 := rl.(lread1);
                                  lwrite0 := rl.(lwrite0); lwrite1 := rl.(lwrite1) |}),
                     REnv.(getenv) r idx,
                     Gamma))
          else k None
      | Read P1 idx =>
        fun k Gamma l =>
          if may_read1 L idx then
            k (Some (Environments.update
                       REnv l idx
                       (fun rl => {| lread0 := rl.(lread1); lread1 := true;
                                  lwrite0 := rl.(lwrite0); lwrite1 := rl.(lwrite1) |}),
                     match (REnv.(getenv) l idx).(lwrite0), (REnv.(getenv) L idx).(lwrite0) with
                     | Some v, _ => v
                     | _, Some v => v
                     | _, _ => REnv.(getenv) r idx
                     end,
                     Gamma))
          else k None
      | Write P0 idx value =>
        fun k =>
          cps value (fun res =>
                       match res with
                       | Some (l, v, Gamma) =>
                         if may_write0 L l idx then
                           k (Some (Environments.update
                                      REnv l idx
                                      (fun rl => {| lread0 := rl.(lread1); lread1 := rl.(lread1);
                                                 lwrite0 := Some v; lwrite1 := rl.(lwrite1) |}),
                                    Ob, Gamma))
                         else
                           k None
                       | None => k None
                       end)
      | Write P1 idx value =>
        fun k =>
          cps value (fun res =>
                       match res with
                       | Some (l, v, Gamma) =>
                         if may_write1 L l idx then
                           k (Some (Environments.update
                                      REnv l idx
                                      (fun rl => {| lread0 := rl.(lread1); lread1 := rl.(lread1);
                                                 lwrite0 := rl.(lwrite0); lwrite1 := Some v |}),
                                    Ob, Gamma))
                         else
                           k None
                       | None => k None
                       end)
      | Unop fn arg1 =>
        fun k =>
          cps arg1 (fun res =>
                      match res with
                      | Some (l, v, Gamma) =>
                        k (Some (l, (PrimSpecs.sigma1 fn) v, Gamma))
                      | None => k None
                      end)
      | Binop fn arg1 arg2 =>
        fun k =>
          cps arg1 (fun res =>
                      match res with
                      | Some (l, v1, Gamma) =>
                        cps arg2 (fun res =>
                                    match res with
                                    | Some (l, v2, Gamma) =>
                                      k (Some (l, (PrimSpecs.sigma2 fn) v1 v2, Gamma))
                                    | None => k None
                                    end) Gamma l
                      | None => k None
                      end)
      | ExternalCall fn arg =>
        fun k =>
          cps arg (fun res =>
                     match res with
                     | Some (l, v, Gamma) =>
                       k (Some (l, (sigma fn) v, Gamma))
                     | None => k None
                     end)
      | InternalCall fn args body => fun k Gamma l => __magic__
      | APos pos a => fun k => cps a k
      end k.

    Definition interp_rule_cps (rl: rule) {A} (k: rule_continuation A) : interpreter A :=
      fun L =>
        interp_action_cps L rl (fun res =>
                                  match res with
                                  | Some (l, _, _) => k (Some l)
                                  | None => k None
                                  end) CtxEmpty log_empty.
  End Action.

  Section Scheduler.
    Context (rules: rule_name_t -> rule).

    Fixpoint interp_scheduler'_cps
             (s: scheduler)
             {A} (k: scheduler_continuation A)
             {struct s} : interpreter A :=
      let interp_try r s1 s2 : interpreter A :=
          fun L =>
            interp_rule_cps (rules r)
                            (fun res =>
                               match res with
                               | Some l => interp_scheduler'_cps s1 k (log_app l L)
                               | None => interp_scheduler'_cps s2 k L
                               end) L in
      match s with
      | Done => k
      | Cons r s => interp_try r s s
      | Try r s1 s2 => interp_try r s1 s2
      | SPos _ s => interp_scheduler'_cps s k
      end.

    Definition interp_scheduler_cps
               (s: scheduler)
               {A} (k: scheduler_continuation A) : A :=
      interp_scheduler'_cps s k log_empty.
  End Scheduler.

  Lemma interp_action_cps_correct:
    forall {sig: tsig var_t}
      {tau}
      (L: Log)
      (a: action sig tau)
      {A} (k: _ -> A)
      (Gamma: tcontext sig)
      (l: Log),
      interp_action_cps L a k Gamma l =
      k (interp_action r sigma Gamma L l a).
  Proof.
    induction a; cbn; intros.
    all: repeat match goal with
                | _ => progress simpl
                | [ H: context[_ = _] |- _ ] => rewrite H
                | [  |- context[interp_action] ] => destruct interp_action as [((?, ?), ?) | ]
                | [  |- context[match ?x with _ => _ end] ] => destruct x
                | _ => reflexivity
                end.
    admit.
  Admitted.

  Lemma interp_action_cps_correct_rev:
    forall {sig: tsig var_t}
      {tau}
      (L: Log)
      (a: action sig tau)
      (Gamma: tcontext sig)
      (l: Log),
      interp_action r sigma Gamma L l a =
      interp_action_cps L a id Gamma l.
  Proof.
    intros; rewrite interp_action_cps_correct; reflexivity.
  Qed.

  Lemma interp_rule_cps_correct:
    forall (L: Log)
      (a: rule)
      {A} (k: _ -> A),
      interp_rule_cps a k L =
      k (interp_rule r sigma L a).
  Proof.
    unfold interp_rule, interp_rule_cps; intros.
    rewrite interp_action_cps_correct.
    destruct interp_action as [((?, ?), ?) | ]; reflexivity.
  Qed.


  Lemma interp_rule_cps_correct_rev:
    forall (L: Log)
      (a: rule),
      interp_rule r sigma L a =
      interp_rule_cps a id L.
  Proof.
    intros; rewrite interp_rule_cps_correct; reflexivity.
  Qed.

  Lemma interp_scheduler'_cps_correct:
    forall (rules: rule_name_t -> rule)
      (s: scheduler)
      (L: Log)
      {A} (k: _ -> A),
      interp_scheduler'_cps rules s k L =
      k (interp_scheduler' r sigma rules L s).
  Proof.
    induction s; cbn; intros.
    all: repeat match goal with
                | _ => progress simpl
                | _ => rewrite interp_rule_cps_correct
                | [ H: context[_ = _] |- _ ] => rewrite H
                | [  |- context[interp_rule] ] => destruct interp_action as [((?, ?), ?) | ]
                | [  |- context[match ?x with _ => _ end] ] => destruct x
                | _ => reflexivity
                end.
  Qed.

  Lemma interp_scheduler_cps_correct:
    forall (rules: rule_name_t -> rule)
      (s: scheduler)
      {A} (k: _ -> A),
      interp_scheduler_cps rules s k =
      k (interp_scheduler r sigma rules s).
  Proof.
    intros; apply interp_scheduler'_cps_correct.
  Qed.

  Definition interp_cycle_cps (rules: rule_name_t -> rule) (s: scheduler) {A} (k: _ -> A) :=
    interp_scheduler_cps rules s (fun L => k (commit_update r L)).

  Definition interp_cycle (rules: rule_name_t -> rule) (s: scheduler) :=
    commit_update r (interp_scheduler r sigma rules s).

  Lemma interp_cycle_cps_correct:
    forall (rules: rule_name_t -> rule)
      (s: scheduler)
      {A} (k: _ -> A),
      interp_cycle_cps rules s k =
      k (interp_cycle rules s).
  Proof.
    unfold interp_cycle, interp_cycle_cps; intros; rewrite interp_scheduler_cps_correct.
    reflexivity.
  Qed.

  Lemma interp_cycle_cps_correct_rev:
    forall (rules: rule_name_t -> rule)
      (s: scheduler),
      interp_cycle rules s =
      interp_cycle_cps rules s id.
  Proof.
    intros; rewrite interp_cycle_cps_correct; reflexivity.
  Qed.

  Section WP.
    Definition action_precondition := action_interpreter Prop.
    Definition action_postcondition := action_continuation Prop.
    Definition precondition := interpreter Prop.
    Definition rule_postcondition := rule_continuation Prop.
    Definition scheduler_postcondition := scheduler_continuation Prop.
    Definition cycle_postcondition := cycle_continuation Prop.

    Definition wp_action {sig tau} (L: Log) (a: action sig tau) (post: action_postcondition sig tau) : action_precondition sig :=
      interp_action_cps L a post.

    Definition wp_rule (rl: rule) (post: rule_postcondition) : precondition :=
      interp_rule_cps rl post.

    Definition wp_scheduler (rules: rule_name_t -> rule) (s: scheduler) (post: scheduler_postcondition) : Prop :=
      interp_scheduler_cps rules s post.

    Definition wp_cycle (rules: rule_name_t -> rule) (s: scheduler) (post: cycle_postcondition) : Prop :=
      interp_cycle_cps rules s post.

    Lemma wp_action_correct:
      forall {sig: tsig var_t}
        {tau}
        (Gamma: tcontext sig)
        (L: Log)
        (l: Log)
        (a: action sig tau)
        (post: action_postcondition sig tau),
        wp_action L a post Gamma l <->
        post (interp_action r sigma Gamma L l a).
    Proof.
      intros; unfold wp_action; rewrite interp_action_cps_correct; reflexivity.
    Qed.

    Lemma wp_rule_correct:
      forall (L: Log)
        (rl: rule)
        (post: rule_postcondition),
        wp_rule rl post L <->
        post (interp_rule r sigma L rl).
    Proof.
      intros; unfold wp_rule; rewrite interp_rule_cps_correct; reflexivity.
    Qed.

    Lemma wp_scheduler_correct:
      forall (rules: rule_name_t -> rule)
        (s: scheduler)
        (post: scheduler_postcondition),
        wp_scheduler rules s post <->
        post (interp_scheduler r sigma rules s).
    Proof.
      intros; unfold wp_scheduler; rewrite interp_scheduler_cps_correct; reflexivity.
    Qed.

    Lemma wp_cycle_correct:
      forall (rules: rule_name_t -> rule)
        (s: scheduler)
        (post: cycle_postcondition),
        wp_cycle rules s post <->
        post (interp_cycle rules s).
    Proof.
      intros; unfold wp_cycle; rewrite interp_cycle_cps_correct; reflexivity.
    Qed.
  End WP.
End CPS.
