(*! Tools | Lemmas pertaining to tools on typed syntax !*)
Require Import Koika.TypedSyntaxFunctions Koika.TypedSemantics.

Section TypedSyntaxProperties.
  Context {pos_t var_t fn_name_t rule_name_t reg_t ext_fn_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.

  Context {R: reg_t -> type}.
  Context {Sigma: ext_fn_t -> ExternalSignature}.

  Context {REnv: Env reg_t}.
  Context (r: REnv.(env_t) R).
  Context (sigma: forall f, Sig_denote (Sigma f)).

  Notation rule := (rule pos_t var_t fn_name_t R Sigma).
  Notation action := (action pos_t var_t fn_name_t R Sigma).
  Notation scheduler := (scheduler pos_t rule_name_t).
  Notation Log := (Log R REnv).

  Lemma bits_to_N_zero:
    forall (tau : type) (cst : tau),
      N.eqb (Bits.to_N (bits_of_value cst)) N.zero = true ->
      bits_of_value cst = Bits.zeroes (type_sz tau).
  Proof.
    intros * Heq%Neqb_ok.
    apply Bits.to_N_inj.
    rewrite Bits.to_N_zeroes.
    assumption.
  Qed.

  Ltac dec_step :=
    match goal with
    | _ => progress intros
    | _ => eassumption || discriminate || reflexivity
    | _ => bool_step || cleanup_step
    | _ => progress (cbn in *; subst)
    | [ H: False |- _ ] => destruct H
    | [ H: Some _ = Some _ |- _ ] => inversion H; subst; clear H
    | [ H: context[let/opt _ := ?x in _] |- _ ] =>
      destruct x as [ ((? & ?) & ?) | ] eqn:?
    | [  |- context[if ?x then _ else _] ] =>
      destruct x eqn:?
    | [ H: context[if ?x then _ else _] |- _ ] =>
      destruct x eqn:?
    | [ H: Some _ = Some _ |- _ ] => inversion H; subst; clear H
    | _ => solve [intuition eauto 3 using bits_to_N_zero]
    end.

  Lemma returns_zero_correct {sig tau} :
    forall (a: action sig tau) (Gamma: tcontext sig) (sched_log: Log) (action_log: Log),
      returns_zero a = true ->
      forall l v G,
        interp_action r sigma Gamma sched_log action_log a = Some (l, v, G) ->
        bits_of_value v = Bits.zeroes (type_sz tau).
  Proof.
    induction a; repeat dec_step.
  Qed.

  Lemma is_pure_correct :
    forall {sig tau} (a: action sig tau) (Gamma: tcontext sig) (sched_log: Log) (action_log: Log),
      is_pure a = true ->
      forall l l' v G,
        l = l' ->
        interp_action r sigma Gamma sched_log action_log a = Some (l', v, G) ->
        l = action_log.
  Proof.
    fix IH 3; destruct a; repeat dec_step.
    assert (forall l l' v G,
               l = l' ->
               interp_args r sigma Gamma sched_log action_log args = Some (l', v, G) ->
               l = action_log).

    { clear dependent a; clear t t2 Heqo.
      revert dependent Gamma.
      revert dependent sched_log.
      revert dependent action_log.
      generalize dependent (rev argspec); clear argspec.
      fix IHargs 2; destruct args; cbn; intros;
        repeat dec_step. }

    etransitivity; [ eapply IH | ].
    all: eauto.
  Qed.

  Lemma action_type_correct {sig tau} (a: action sig tau):
    forall tau', action_type a = Some tau' -> tau = tau'.
  Proof. destruct a; cbn; inversion 1; reflexivity. Qed.

  Lemma is_tt_correct {sig tau} :
    forall (a: action sig tau) (Gamma: tcontext sig) (sched_log: Log) (action_log: Log),
      is_tt a = true ->
      tau = unit_t /\
      forall l v G,
       interp_action r sigma Gamma sched_log action_log a = Some (l, v, G) ->
       bits_of_value v = Bits.zeroes (type_sz tau).
  Proof.
    unfold is_tt;
    repeat match goal with
           | _ => dec_step
           | [  |- _ /\ _ ] => split
           | [ H: vect_nil_t _ |- _ ] => destruct H
           | [ H: context[beq_dec] |- _ ] => rewrite beq_dec_iff in H
           | [ H: context[action_type _] |- _ ] => apply action_type_correct in H
           | [ H: is_pure ?a = true |- _ ] => pose proof (is_pure_correct _ _ _ _ H)
           | [ H: is_pure ?a = true |- context[interp_action _ _ ?G ?L ?l ?a]] =>
             pose proof (is_pure_correct a G L l H); clear H;
               destruct interp_action as [ ((? & ?) & ?) | ] eqn:?
           end.
  Qed.

  Lemma interp_arithmetic_correct {sig tau} :
    forall (a: action sig tau) (Gamma: tcontext sig) (sched_log: Log) (action_log: Log) res,
      interp_arithmetic a = Some res ->
      forall l v G,
      interp_action r sigma Gamma sched_log action_log a = Some (l, v, G) ->
      v = res.
  Proof.
    induction a;
      repeat match goal with
             | _ => dec_step
             | [ H: context[opt_bind ?x] |- _ ] => destruct x
             | _ => f_equal
             end.
  Qed.
End TypedSyntaxProperties.
