Require Import SGA.Common SGA.Syntax SGA.Semantics SGA.Types SGA.Typechecking.

Definition fenv_tenv_consistent {K V V'} `{EV: Env K V} (ev: env_t EV) (fv: fenv K V') :=
  (forall k v, fv k v -> exists v', getenv ev k = v') /\
  (forall k v, getenv ev k = Some v -> exists v', fv k v').

Section TypeSafety.
  Context {TVar: Type}.
  Context {TFn: Type}.

  Context (GammaEnv: Env TVar value).
  Context (SigmaEnv: Env TFn ExternalFunction).

Definition correct_type (r: result (Log * value)) (tau: type) :=
  match r with
  | Success (_, v) => type_of_value v = tau
  | CannotRun => True
  | Stuck => False
  end.

Ltac not_stuck :=
  intros; unfold may_write, may_read0, may_read1;
  repeat match goal with
         | [  |- match ?x with _ => _ end <> Stuck ] => destruct x
         end;
  discriminate.

Hint Transparent not.

Lemma may_write_not_stuck sched_log rule_log level idx :
    may_write sched_log rule_log level idx <> Stuck.
Proof. not_stuck. Qed.

Lemma may_read0_not_stuck sched_log rule_log idx :
    may_read0 sched_log rule_log idx <> Stuck.
Proof. not_stuck. Qed.

Lemma may_read1_not_stuck sched_log rule_log idx :
    may_read1 sched_log rule_log idx <> Stuck.
Proof. not_stuck. Qed.

Hint Extern 1 False => eapply may_write_not_stuck : types.
Hint Extern 1 False => eapply may_read0_not_stuck : types.
Hint Extern 1 False => eapply may_read1_not_stuck : types.

Lemma type_of_value_le_eq :
  forall tau tau' v,
    type_le tau tau' ->
    type_of_value v = tau' ->
    type_of_value v = tau.
Proof.
  destruct v; cbn; inversion 1; congruence.
Qed.

Lemma type_safety :
  forall (Gamma__types: fenv _ _) V sched_log
    Sigma Sigma__reg Sigma__fn,
    fenv_tenv_consistent Sigma Sigma__fn ->
    forall (s: syntax TVar TFn)
      (tau: Types.type) ,
      Typechecking.HasType
        Sigma__reg Sigma__fn
        Gamma__types s tau ->
      forall (rule_log: Log)
        (Gamma: GammaEnv.(env_t)),
        fenv_tenv_consistent Gamma Gamma__types ->
        correct_type (interp Sigma Gamma V sched_log rule_log s) tau.
Proof.
  induction 2; cbn; intros.

  Ltac t :=
    repeat match goal with
           | _ => discriminate
           | _ => progress (cbn; intros)
           | [ p: _ * _ |- _ ] => destruct p
           | [  |- _ (opt_result _ ?o) _] =>
             destruct o eqn:?
           | [  |- correct_type (result_bind ?r _) _ ] =>
             destruct r eqn:?
           | [  |- correct_type (result_map ?r _) _ ] =>
             destruct r eqn:?
           | [  |- correct_type ((if ?v then _ else _)) _ ] =>
             destruct v eqn:?
           | [ H: forall _ _, fenv_tenv_consistent _ ?Gamma -> _,
                 H': fenv_tenv_consistent _ ?Gamma |- _ ] =>
             specialize (fun log => H log _ H')
           | [ H: forall log, correct_type (interp _ ?Gamma _ _ log ?s) _,
                 l: Log |- _ ] =>
             pose_once (H l)
           | [ H: correct_type (interp _ ?Gamma _ _ ?log ?s) _,
                  H': interp _ ?Gamma _ _ ?log ?s = Stuck |- _ ] =>
             red in H; rewrite H' in H
           | _ => eauto with types
           end;
    repeat match goal with
           | [ H: Posed _ |- _ ] => clear H
           end.

  all: try solve [t].

  - t.
    destruct (interp Sigma Gamma0 V sched_log rule_log s) as [ (? & ?) | | ]; cbn in *;
      eauto using type_of_value_le_eq.
  - t.
    apply IHHasType2.
    admit.                    (* Consistent *)
  - t.

    Lemma type_of_value_consistent:
      forall (Gamma : fenv TVar type) (var : TVar) (tau : type),
        Gamma var tau ->
        forall Gamma0 : env_t GammaEnv,
          fenv_tenv_consistent Gamma0 Gamma ->
          forall a : value,
            opt_result Stuck (getenv Gamma0 var) = Success a ->
            type_of_value a = tau.
    Proof.
      intros * HGamma * (? & Hconsistent) * HSuccess.
      red in Hconsistent.
      
      intros Gamma var tau H0 Gamma0 H1 a Heqr.
      
    Lemma 
    admit.                    (* Gamma well typed *)
    admit.                    (* Gamma consistent *)
  - t.
    admit.                    (* Sigma__reg well typed *)
    admit.                    (* Sigma__reg consistent *)

    admit.                    (* Combination of well-typed Sigma__reg and log *)

    (* FIXME add well-typed log hyp; compute sigmareg and sigmafn from V and Sigma *)
    admit.                    (* Sigma__reg consistent *)

  - t.
    admit.                    (* Sigma__reg consistent with V *)
    admit.                    (* Sigma__reg consistent with V *)

  - t.

    admit.                    (* fns produce advertised values *)
    admit.                    (* argvs have right length and types *)
    admit.                    (* Fold can't get stuck *)
    admit.                    (* Sigma consistent *)
Admitted.

