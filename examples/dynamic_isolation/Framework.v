Require Import dynamic_isolation.Tactics.
Require Import Coq.Lists.List.
Import ListNotations.

Section StepFramework.
  Section Parameterised.
    Context {state_t event_t: Type}.
    Context (initial_state: state_t).
    Context (step_fn: state_t -> state_t * event_t).

    Fixpoint step_n (n: nat) : state_t * list event_t :=
      match n with
      | 0 => (initial_state, [])
      | S n' =>
          let (st, evs) := step_n n' in
          let (st', ev) := step_fn st in
          (st', evs ++ [ev])
      end.

  End Parameterised.

  Section Projection.
    Context {state_t event_t: Type}.
    Context {state_t' : Type}.
    Context (initial_state: state_t).
    Context (initial_state': state_t').
    Context (step_fn: state_t -> state_t * event_t).
    Context (step_fn': state_t' -> state_t' * event_t).
    Context (proj_st: state_t -> state_t').
    (* Context (pf_proj_initial: proj_st initial_state = initial_state'). *)

    Definition is_proj (st: state_t) (st': state_t') : Prop :=
      proj_st st = st'.

    Definition natural_step_fn :=
      forall st st',
      is_proj st st' ->
      is_proj (fst (step_fn st)) (fst (step_fn' st')) /\ (snd (step_fn st) = snd (step_fn' st')).

    Context (pf_proj_initial: is_proj initial_state initial_state').
    Context (pf_natural_step: natural_step_fn).

    Lemma proj_step_fn_eq: forall (n: nat) (st: state_t) (st': state_t') (evs evs': list event_t),
      step_n initial_state step_fn n = (st, evs) ->
      step_n initial_state' step_fn' n = (st', evs') ->
      st' = proj_st st /\ evs = evs'.
    Proof.
      induction n; intros; simplify_all.
      destruct_all_matches; simplify_all.
      specialize IHn with (1 := eq_refl) (2 := eq_refl); propositional; subst.
      consider natural_step_fn.
      specialize pf_natural_step with (st := s1) (st' := proj_st s1).
      rewrite Heqp2 in *. rewrite Heqp0 in *. simpl in *.
      consider is_proj.
      destruct pf_natural_step; subst; auto.
    Qed.

  End Projection.

End StepFramework.
