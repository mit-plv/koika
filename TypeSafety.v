Require Import SGA.Common SGA.Syntax SGA.Semantics SGA.Types.

Definition type_of_value (v: value) :=
  match v with
  | vtt => unit_t
  | vbits bits => bit_t (length bits)
  end.

Definition fenv_tenv_consistent {K V V'} `{EV: Env K V} (ev: env_t EV) (fv: fenv K V') :=
  (forall k v, fv k v -> exists v', getenv ev k = v') /\
  (forall k v, getenv ev k = Some v -> exists v', fv k v').

Section TypeSafety.
  Section Interp.
  Context {TVar: Type}.
  Context {TFn: Type}.

  Context (GammaEnv: Env TVar value).
  Context (SigmaEnv: Env TFn (list value -> option value)).

Definition fns_welltyped (Sigma: SigmaEnv.(env_t)) (Sigma__fn: fenv _ _) :=
  forall idx fn argTypes retType,
    getenv Sigma idx = Some fn ->
    Sigma__fn idx (SigFn argTypes retType) ->
    forall args,
      List.length args = List.length argTypes ->
      (forall (n: nat) (v: value) (tau: type),
          List.nth_error args n = Some v ->
          List.nth_error argTypes n = Some tau ->
          type_of_value v = tau) ->
      fn args <> None.

(* Generalizable Variables K V. *)

(* Definition fenv_of_env {V'} `{EV: Env K V} (f: V -> V') (ev: env_t EV) : fenv K V' := *)
(*   {| fn k v := match getenv ev k with *)
(*               | Some v0 => f v0 = v *)
(*               | None => False *)
(*               end; *)
(*      uniq := ltac:(cbn; intros; destruct (getenv ev k); (congruence || tauto)) |}. *)


(* Lemma progress' : *)
(*   forall (Sigma: SigmaEnv.(env_t)) (Gamma__types: fenv _ _) *)
(*     Sigma__reg Sigma__fn, *)
(*     fenv_tenv_consistent Sigma Sigma__fn -> *)
(*     fns_welltyped Sigma Sigma__fn -> *)
(*     forall (s: syntax TVar TFn) *)
(*       (tau: Types.type) , *)
(*       Types.HasType *)
(*         Sigma__reg Sigma__fn *)
(*         Gamma__types s tau -> *)
(*       forall (rule_log: Log) *)
(*         (Gamma: GammaEnv.(env_t)), *)
(*         fenv_tenv_consistent Gamma Gamma__types -> *)
(*         interp _ _ Sigma V rule_log  s Gamma <> Stuck. *)
(*   induction 3. *)
(*   - eauto. *)
(*   - *)

(*     repeat match goal with *)
(*            | _ => discriminate *)
(*            | _ => progress (cbn; intros) *)
(*            | [ p: _ * _ |- _ ] => destruct p *)
(*            | [  |- _ (opt_result _ ?o) _ <> Stuck ] => *)
(*              destruct o eqn:? *)
(*            | [  |- result_bind ?r _ <> Stuck ] => *)
(*              destruct r eqn:? *)
(*            | [  |- result_map ?r _ <> Stuck ] => *)
(*              destruct r eqn:? *)
(*            | [  |- (if ?v then _ else _) <> Stuck ] => *)
(*              destruct v eqn:? *)
(*            | [ H: forall _ _, fenv_tenv_consistent _ ?Gamma -> _, *)
(*                  H': fenv_tenv_consistent _ ?Gamma |- _ ] => *)
(*              specialize (fun log => H log _ H') *)
(*            | [ H: forall log, interp ?Gamma log ?s <> Stuck, *)
(*                  H': interp ?Gamma _ ?s = Stuck |- _ ] => *)
(*              elim (H _ H') *)
(*            | _ => eauto *)
(*            end. *)

(*     apply IHHasType2. *)

(*     admit. *)
(*   - *)

(*     repeat match goal with *)
(*            | _ => discriminate *)
(*            | _ => progress (cbn; intros) *)
(*            | [ p: _ * _ |- _ ] => destruct p *)
(*            | [  |- _ (opt_result _ ?o) _ <> Stuck ] => *)
(*              destruct o eqn:? *)
(*            | [  |- result_bind ?r _ <> Stuck ] => *)
(*              destruct r eqn:? *)
(*            | [  |- result_map ?r _ <> Stuck ] => *)
(*              destruct r eqn:? *)
(*            | [  |- (if ?v then _ else _) <> Stuck ] => *)
(*              destruct v eqn:? *)
(*            | [ H: forall _ _, fenv_tenv_consistent _ ?Gamma -> _, *)
(*                  H': fenv_tenv_consistent _ ?Gamma |- _ ] => *)
(*              specialize (fun log => H log _ H') *)
(*            | [ H: forall log, interp ?Gamma log ?s <> Stuck, *)
(*                  H': interp ?Gamma _ ?s = Stuck |- _ ] => *)
(*              elim (H _ H') *)
(*            | _ => eauto *)
(*            end. *)

(*     admit. *)

(*   - repeat match goal with *)
(*            | _ => discriminate *)
(*            | _ => progress (cbn; intros) *)
(*            | [ p: _ * _ |- _ ] => destruct p *)
(*            | [  |- _ (opt_result _ ?o) _ <> Stuck ] => *)
(*              destruct o eqn:? *)
(*            | [  |- result_bind ?r _ <> Stuck ] => *)
(*              destruct r eqn:? *)
(*            | [  |- result_map ?r _ <> Stuck ] => *)
(*              destruct r eqn:? *)
(*            | [  |- (if ?v then _ else _) <> Stuck ] => *)
(*              destruct v eqn:? *)
(*            | [ H: forall _ _, fenv_tenv_consistent _ ?Gamma -> _, *)
(*                  H': fenv_tenv_consistent _ ?Gamma |- _ ] => *)
(*              specialize (fun log => H log _ H') *)
(*            | [ H: forall log, interp ?Gamma log ?s <> Stuck, *)
(*                  H': interp ?Gamma _ ?s = Stuck |- _ ] => *)
(*              elim (H _ H') *)
(*            | _ => eauto *)
(*            end. *)

(*   - repeat match goal with *)
(*            | _ => discriminate *)
(*            | _ => progress (cbn; intros) *)
(*            | [ p: _ * _ |- _ ] => destruct p *)
(*            | [  |- _ (opt_result _ ?o) _ <> Stuck ] => *)
(*              destruct o eqn:? *)
(*            | [  |- result_bind ?r _ <> Stuck ] => *)
(*              destruct r eqn:? *)
(*            | [  |- result_map ?r _ <> Stuck ] => *)
(*              destruct r eqn:? *)
(*            | [  |- (if ?v then _ else _) <> Stuck ] => *)
(*              destruct v eqn:? *)
(*            | [ H: forall _ _, fenv_tenv_consistent _ ?Gamma -> _, *)
(*                  H': fenv_tenv_consistent _ ?Gamma |- _ ] => *)
(*              specialize (fun log => H log _ H') *)
(*            | [ H: forall log, interp ?Gamma log ?s <> Stuck, *)
(*                  H': interp ?Gamma _ ?s = Stuck |- _ ] => *)
(*              elim (H _ H') *)
(*            | _ => eauto *)
(*            end. *)

(*   - repeat match goal with *)
(*            | _ => discriminate *)
(*            | _ => progress (cbn; intros) *)
(*            | [ p: _ * _ |- _ ] => destruct p *)
(*            | [  |- _ (opt_result _ ?o) _ <> Stuck ] => *)
(*              destruct o eqn:? *)
(*            | [  |- result_bind ?r _ <> Stuck ] => *)
(*              destruct r eqn:? *)
(*            | [  |- result_map ?r _ <> Stuck ] => *)
(*              destruct r eqn:? *)
(*            | [  |- (if ?v then _ else _) <> Stuck ] => *)
(*              destruct v eqn:? *)
(*            | [ H: forall _ _, fenv_tenv_consistent _ ?Gamma -> _, *)
(*                  H': fenv_tenv_consistent _ ?Gamma |- _ ] => *)
(*              specialize (fun log => H log _ H') *)
(*            | [ H: forall log, interp ?Gamma log ?s <> Stuck, *)
(*                  H': interp ?Gamma _ ?s = Stuck |- _ ] => *)
(*              elim (H _ H') *)
(*            | _ => eauto *)
(*            end. *)

(*   - repeat match goal with *)
(*            | _ => discriminate *)
(*            | _ => progress (cbn; intros) *)
(*            | [ p: _ * _ |- _ ] => destruct p *)
(*            | [  |- _ (opt_result _ ?o) _ <> Stuck ] => *)
(*              destruct o eqn:? *)
(*            | [  |- result_bind ?r _ <> Stuck ] => *)
(*              destruct r eqn:? *)
(*            | [  |- result_map ?r _ <> Stuck ] => *)
(*              destruct r eqn:? *)
(*            | [  |- (if ?v then _ else _) <> Stuck ] => *)
(*              destruct v eqn:? *)
(*            | [ H: forall _ _, fenv_tenv_consistent _ ?Gamma -> _, *)
(*                  H': fenv_tenv_consistent _ ?Gamma |- _ ] => *)
(*              specialize (fun log => H log _ H') *)
(*            | [ H: forall log, interp ?Gamma log ?s <> Stuck, *)
(*                  H': interp ?Gamma _ ?s = Stuck |- _ ] => *)
(*              elim (H _ H') *)
(*            | _ => eauto *)
(*            end. *)

(*   - repeat match goal with *)
(*            | _ => discriminate *)
(*            | _ => progress (cbn; intros) *)
(*            | [ p: _ * _ |- _ ] => destruct p *)
(*            | [  |- _ (opt_result _ ?o) _ <> Stuck ] => *)
(*              destruct o eqn:? *)
(*            | [  |- result_bind ?r _ <> Stuck ] => *)
(*              destruct r eqn:? *)
(*            | [  |- result_map ?r _ <> Stuck ] => *)
(*              destruct r eqn:? *)
(*            | [  |- (if ?v then _ else _) <> Stuck ] => *)
(*              destruct v eqn:? *)
(*            | [ H: forall _ _, fenv_tenv_consistent _ ?Gamma -> _, *)
(*                  H': fenv_tenv_consistent _ ?Gamma |- _ ] => *)
(*              specialize (fun log => H log _ H') *)
(*            | [ H: forall log, interp ?Gamma log ?s <> Stuck, *)
(*                  H': interp ?Gamma _ ?s = Stuck |- _ ] => *)
(*              elim (H _ H') *)
(*            | _ => eauto *)
(*            end. *)

(*     (* Sigma__reg consistent *) *)
(*     exfalso; admit. *)

(*     (* may_read stuck *) *)
(*     exfalso; admit. *)

(*     (* Sigma__reg consistent *) *)
(*     exfalso; admit. *)

(*     (* may_read stuck *) *)
(*     exfalso; admit. *)


(*   - repeat match goal with *)
(*            | _ => discriminate *)
(*            | _ => progress (cbn; intros) *)
(*            | [ p: _ * _ |- _ ] => destruct p *)
(*            | [  |- _ (opt_result _ ?o) _ <> Stuck ] => *)
(*              destruct o eqn:? *)
(*            | [  |- result_bind ?r _ <> Stuck ] => *)
(*              destruct r eqn:? *)
(*            | [  |- result_map ?r _ <> Stuck ] => *)
(*              destruct r eqn:? *)
(*            | [  |- (if ?v then _ else _) <> Stuck ] => *)
(*              destruct v eqn:? *)
(*            | [ H: forall _ _, fenv_tenv_consistent _ ?Gamma -> _, *)
(*                  H': fenv_tenv_consistent _ ?Gamma |- _ ] => *)
(*              specialize (fun log => H log _ H') *)
(*            | [ H: forall log, interp ?Gamma log ?s <> Stuck, *)
(*                  H': interp ?Gamma _ ?s = Stuck |- _ ] => *)
(*              elim (H _ H') *)
(*            | _ => eauto *)
(*            end. *)

(*     exfalso; admit.           (* may_write doesn't get stuck *) *)

(*   - repeat match goal with *)
(*            | _ => discriminate *)
(*            | _ => progress (cbn; intros) *)
(*            | [ p: _ * _ |- _ ] => destruct p *)
(*            | [  |- _ (opt_result _ ?o) _ <> Stuck ] => *)
(*              destruct o eqn:? *)
(*            | [  |- result_bind ?r _ <> Stuck ] => *)
(*              destruct r eqn:? *)
(*            | [  |- result_map ?r _ <> Stuck ] => *)
(*              destruct r eqn:? *)
(*            | [  |- (if ?v then _ else _) <> Stuck ] => *)
(*              destruct v eqn:? *)
(*            | [ H: forall _ _, fenv_tenv_consistent _ ?Gamma -> _, *)
(*                  H': fenv_tenv_consistent _ ?Gamma |- _ ] => *)
(*              specialize (fun log => H log _ H') *)
(*            | [ H: forall log, interp ?Gamma log ?s <> Stuck, *)
(*                  H': interp ?Gamma _ ?s = Stuck |- _ ] => *)
(*              elim (H _ H') *)
(*            | _ => eauto *)
(*            end. *)

(*     (* Types are good but fn returns None *) *)
(*     admit. *)

(*     (* Consistent *) *)
(*     admit. *)

(*     (* Fold stuck despite proper types *) *)
(*     admit. *)
(* Admitted. *)

(* Lemma progress : *)
(*   forall (Gamma__types: fenv _ _) (Gamma: GammaEnv.(env_t)) Sigma__reg Sigma__fn, *)
(*     fenv_tenv_consistent Sigma Sigma__fn -> *)
(*     fenv_tenv_consistent Gamma Gamma__types -> *)
(*     fns_welltyped Sigma__fn -> *)
(*     forall (s: syntax TVar TFn) *)
(*       (tau: Types.type), *)
(*       Types.HasType Sigma__reg Sigma__fn Gamma__types s tau -> *)
(*       forall (rule_log: Log), *)
(*         interp Gamma rule_log s <> Stuck. *)
(* Proof. *)
(*   eauto using progress'. *)
(* Qed. *)

Definition correct_type (r: result (Log * value)) (tau: type) :=
  match r with
  | Success (_, v) => type_of_value v = tau
  | CannotRun => True
  | Stuck => False
  end.

Lemma progress'' :
  forall (Gamma__types: fenv _ _) V sched_log
    Sigma Sigma__reg Sigma__fn,
    fenv_tenv_consistent Sigma Sigma__fn ->
    fns_welltyped Sigma Sigma__fn ->
    forall (s: syntax TVar TFn)
      (tau: Types.type) ,
      Types.HasType
        Sigma__reg Sigma__fn
        Gamma__types s tau ->
      forall (rule_log: Log)
        (Gamma: GammaEnv.(env_t)),
        fenv_tenv_consistent Gamma Gamma__types ->
        correct_type (interp Sigma Gamma V sched_log rule_log s) tau.
Proof.
  induction 3; cbn; intros.

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
                 H': interp _ ?Gamma _ _ ?log ?s = Stuck |- _ ] =>
             specialize (H log); red in H;
             rewrite H' in H
           | _ => eauto
           end.

  all: try solve [t].


  - t.
    admit.                    (* tau must be = tau' since it can't be any *)
  - t.
    apply IHHasType2.
    admit.                    (* Consistent *)
  - t.
    admit.                    (* Gamma well typed *)
    admit.                    (* Gamma consistent *)
  - t.
    admit.                    (* Sigma__reg well typed *)
    admit.                    (* Sigma__reg consistent *)
    admit.                    (* may read doesn't get stuck *)

    admit.                    (* Combination of well-typed Sigma__reg and log *)

    (* FIXME add well-typed log hyp *)
    admit.                    (* Sigma__reg consistent *)

    admit.                    (* may read doesn't get stuck *)

  - t.
    admit.                    (* may write doesn't get stuck *)

  - t.

    admit.                    (* fns well typed *)
    admit.                    (* fns don't get stuck *)
    admit.                    (* Sigma__fn consistent *)
    admit.                    (* Fold can't get stuck *)
Admitted.

