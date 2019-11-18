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

  Lemma is_const_zero_correct {sig tau} :
    forall (a: action sig tau) (Gamma: vcontext sig) (sched_log: Log) (action_log: Log),
      is_const_zero a = true ->
      match interp_action r sigma Gamma sched_log action_log a with
      | Some (_, v, _) => bits_of_value v = Bits.zeroes (type_sz tau)
      | None => True
      end.
  Proof.
    induction a; cbn; intros; try discriminate;
      repeat match goal with
             | [ H: (forall Gamma L l, _ -> match interp_action ?r ?sigma Gamma L l ?a with _ => _ end)
                 |- context[interp_action ?r ?sigma ?Gamma ?L ?l ?a] ] =>
               specialize (H Gamma L l)
             | [ H: is_const_zero ?x = true -> _, H': is_const_zero ?x = true |- _ ] =>
               specialize (H H')
             | [  |- context[opt_bind (interp_action ?r ?sigma ?Gamma ?sched_log ?action_log ?a) _] ] =>
               destruct (interp_action r sigma Gamma sched_log action_log a) as [ ((? & ?) & ?) | ]
             | [ H: _ && _ = _ |- _ ] => apply andb_prop in H; destruct H
             | [  |- context[if ?c then _ else _] ] => destruct c
             | _ => eauto using bits_to_N_zero || simpl
             end.
  Qed.
End TypedSyntaxProperties.
