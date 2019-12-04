(*! Tools | Lemmas pertaining to tools on typed syntax !*)
Require Import Koika.TypedSyntaxTools Koika.Semantics.

Section TypedSyntaxProperties.
  Context {pos_t var_t rule_name_t reg_t ext_fn_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.

  Context {R: reg_t -> type}.
  Context {Sigma: ext_fn_t -> ExternalSignature}.

  Context {REnv: Env reg_t}.
  Context (r: REnv.(env_t) R).
  Context (sigma: forall f, Sig_denote (Sigma f)).

  Notation rule := (rule pos_t var_t R Sigma).
  Notation action := (action pos_t var_t R Sigma).
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
    | _ => eassumption || discriminate || reflexivity
    | _ => bool_step || cleanup_step
    | _ => progress (cbn in *; subst)
    | [ H: False |- _ ] => destruct H
    | [ H: Some _ = Some _ |- _ ] => inversion H; subst; clear H
    | [ H: context[let/opt _ := ?x in _] |- _ ] => destruct x eqn:?
    | [  |- context[if ?x then _ else _] ] => destruct x eqn:?
    | _ => solve [eauto]
    end.

  Lemma returns_zero_correct {sig tau} :
    forall (a: action sig tau) (Gamma: vcontext sig) (sched_log: Log) (action_log: Log),
      returns_zero a = true ->
      match interp_action r sigma Gamma sched_log action_log a with
      | Some (_, v, _) => bits_of_value v = Bits.zeroes (type_sz tau)
      | None => True
      end.
  Proof.
    induction a; cbn; intros; try discriminate;
      repeat match goal with
             | _ => dec_step
             | [ H: (forall Gamma L l, _ -> match interp_action ?r ?sigma Gamma L l ?a with _ => _ end)
                 |- context[interp_action ?r ?sigma ?Gamma ?L ?l ?a] ] =>
               specialize (H Gamma L l)
             | [ H: returns_zero ?x = true -> _, H': returns_zero ?x = true |- _ ] =>
               specialize (H H')
             | [  |- context[opt_bind (interp_action ?r ?sigma ?Gamma ?sched_log ?action_log ?a) _] ] =>
               destruct (interp_action r sigma Gamma sched_log action_log a) as [ ((? & ?) & ?) | ]
             | _ => eauto using bits_to_N_zero || simpl
             end.
  Qed.

  Lemma is_pure_correct {sig tau} :
    forall (a: action sig tau) (Gamma: vcontext sig) (sched_log: Log) (action_log: Log),
      is_pure a = true ->
      match interp_action r sigma Gamma sched_log action_log a with
      | Some (l, _, _) => l = action_log
      | None => False
      end.
  Proof.
    induction a; cbn; intros; try discriminate;
    repeat match goal with
           | _ => dec_step
           | [ H: (forall Gamma sched_log action_log,
                      _ -> match interp_action ?r ?sigma Gamma sched_log action_log ?a with
                          | _ => _ end) |-
               context[interp_action ?r ?sigma ?Gamma ?sched_log ?action_log ?a] ] =>
             specialize (H Gamma sched_log action_log ltac:(eauto));
               destruct (interp_action r sigma Gamma sched_log action_log a)
               as [ ((? & ?) & ?) | ] eqn:?
           end.
  Qed.

  Lemma action_type_correct {sig tau} (a: action sig tau):
    forall tau', action_type a = Some tau' -> tau = tau'.
  Proof. destruct a; cbn; inversion 1; reflexivity. Qed.

  Lemma is_tt_correct {sig tau} :
    forall (a: action sig tau) (Gamma: vcontext sig) (sched_log: Log) (action_log: Log),
      is_tt a = true ->
      tau = unit_t /\
      match interp_action r sigma Gamma sched_log action_log a with
      | Some (_, v, _) => bits_of_value v = Bits.zeroes (type_sz tau)
      | None => False
      end.
  Proof.
    unfold is_tt; intros.
    repeat match goal with
           | _ => dec_step
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
    forall (a: action sig tau) (Gamma: vcontext sig) (sched_log: Log) (action_log: Log) res,
      interp_arithmetic a = Some res ->
      match interp_action r sigma Gamma sched_log action_log a with
      | Some (_, v, _) => v = res
      | None => True
      end.
  Proof.
    induction a; cbn; intros;
    repeat match goal with
           | _ => dec_step
           | [ H: (forall Gamma sched_log action_log _,
                      _ -> match interp_action ?r ?sigma Gamma sched_log action_log ?a with
                          | _ => _ end) |-
               context[interp_action ?r ?sigma ?Gamma ?sched_log ?action_log ?a] ] =>
             specialize (H Gamma sched_log action_log _ ltac:(eauto));
               destruct (interp_action r sigma Gamma sched_log action_log a)
               as [ ((? & ?) & ?) | ] eqn:?
           end.
  Qed.
End TypedSyntaxProperties.
