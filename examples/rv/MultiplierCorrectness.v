(*! Proof of correctness of the multiplier module !*)

Require Import Koika.Frontend Koika.Std Koika.ProgramTactics.
Require Export rv.Multiplier.
Require Import Lia.

Module MultiplierProofs.
  Module Sig32 <: Multiplier_sig.
    Definition n := 32.
  End Sig32.
  Module mul32 := ShiftAddMultiplier Sig32.
  Import mul32.
  Import Sig32.

  Definition default := ContextEnv.(create) r.

  Definition typed_enq :=
    tc_function R empty_Sigma enq.

  Definition typed_step :=
    tc_function R empty_Sigma step.

  Definition typed_deq :=
    tc_function R empty_Sigma deq.

  Notation all_regs :=
    [valid; operand1; operand2; result; n_step; finished].

  Definition partial_mul (a b n_step: N) :=
    (a * (b mod (2 ^ n_step)))%N.

  Lemma mod_succ_add (a n: N) :
    (a mod (2 ^ N.succ n) = a mod 2 ^ n + (N.b2n (N.testbit a n)) * 2 ^ n)%N.
  Proof.
    rewrite N.pow_succ_r'.
    rewrite (N.div_mod' a (2 ^ n)) at 1.
    rewrite N.testbit_spec'.
    rewrite N.add_mod by (destruct n; cbn; lia).
    rewrite (N.mul_comm 2 (2 ^ n)).
    rewrite N.mul_mod_distr_l by (destruct n; cbn; lia).
    rewrite (N.mod_small (a mod 2 ^ n)).
    - rewrite N.mod_small; [ ring | ].
      eapply N.le_lt_trans.
      + apply N.add_le_mono.
        * apply N.mul_le_mono_l, N.lt_le_pred.
          apply N.mod_upper_bound. lia.
        * apply N.lt_le_pred, N.mod_lt. destruct n; cbn; lia.
      + cbn. rewrite N.mul_1_r. rewrite N.pred_sub.
        enough (2 ^ n > 0)%N by lia.
        destruct n; cbn; lia.
    - eapply N.lt_trans.
      + apply N.mod_lt.
        destruct n; discriminate.
      + rewrite <-(N.mul_1_r (2 ^ n)) at 1.
        apply N.mul_lt_mono_pos_l; destruct n; cbn; lia.
  Qed.

  Lemma partial_mul_step (a b n_step: N) :
    partial_mul a b (N.succ n_step) =
    ((partial_mul a b n_step) +
     a * (N.b2n (N.testbit b n_step) * (2 ^ n_step)))%N.
  Proof.
    unfold partial_mul.
    rewrite mod_succ_add.
    ring.
  Qed.

  Lemma mul_to_partial_mul :
    forall n x y,
      (y < 2 ^ n)%N ->
      (x * y = partial_mul x y n)%N.
  Proof.
    intros.
    unfold partial_mul.
    rewrite N.mod_small; auto.
  Qed.

  Definition step_invariant (reg: ContextEnv.(env_t) R) :=
    (Bits.to_N (ContextEnv.(getenv) reg n_step) < N.of_nat n)%N.

  Definition finished_invariant (reg: ContextEnv.(env_t) R) :=
    let valid_val := Bits.to_N (ContextEnv.(getenv) reg valid) in
    let finished_val := Bits.to_N (ContextEnv.(getenv) reg finished) in
    valid_val = 0%N -> finished_val = 0%N.

  Definition result_invariant (reg: ContextEnv.(env_t) R) :=
    let valid_val := Bits.to_N (ContextEnv.(getenv) reg valid) in
    let finished_val := Bits.to_N (ContextEnv.(getenv) reg finished) in
    let result_val := Bits.to_N (ContextEnv.(getenv) reg result) in
    let op1_val := Bits.to_N (ContextEnv.(getenv) reg operand1) in
    let op2_val := Bits.to_N (ContextEnv.(getenv) reg operand2) in
    let n_step_val := Bits.to_N (ContextEnv.(getenv) reg n_step) in
    valid_val = 1%N ->
    finished_val = 0%N ->
    result_val = partial_mul op1_val op2_val n_step_val.

  Definition result_finished_invariant (reg: ContextEnv.(env_t) R) :=
    let finished_val := Bits.to_N (ContextEnv.(getenv) reg finished) in
    let result_val := Bits.to_N (ContextEnv.(getenv) reg result) in
    let op1_val := Bits.to_N (ContextEnv.(getenv) reg operand1) in
    let op2_val := Bits.to_N (ContextEnv.(getenv) reg operand2) in
    finished_val = 1%N ->
    (result_val = op1_val * op2_val)%N.

  Definition invariant reg :=
    step_invariant reg /\
    finished_invariant reg /\
    result_invariant reg /\
    result_finished_invariant reg.

  (** Interpret all possible branches of an action **)
  Lemma enq_preserves_invariant :
    forall env Gamma sched_log action_log action_log_new v Gamma_new,
      interp_action env empty_sigma Gamma sched_log action_log typed_enq =
        Some (action_log_new, v, Gamma_new) ->
      no_latest_writes action_log all_regs ->
      invariant (commit_update env sched_log) ->
      invariant (commit_update env (log_app action_log_new sched_log)).
  Proof.
    intros.
    unfold invariant, step_invariant, finished_invariant,
           result_invariant, result_finished_invariant in *.
    interp_action_all_t.
    Bits_to_N_t.
    repeat (split).
    - discriminate.
    - intros.
      unfold partial_mul. cbn.
      rewrite N.mod_1_r.
      ring.
    - intros.
      match goal with
      | [ H1: ?x = ?y, H2: _ -> ?x = ?z |- _ ] =>
        rewrite H2 in H1 by auto
      end.
      discriminate.
  Qed.

  Lemma deq_preserves_invariant :
    forall env Gamma sched_log action_log action_log_new v Gamma_new,
      interp_action env empty_sigma Gamma sched_log action_log typed_deq =
        Some (action_log_new, v, Gamma_new) ->
      no_latest_writes action_log all_regs ->
      invariant (commit_update env sched_log) ->
      invariant (commit_update env (log_app action_log_new sched_log)).
  Proof.
    intros.
    unfold invariant, step_invariant, finished_invariant, result_invariant in *.
    interp_action_all_t.
    Bits_to_N_t.
    repeat (split); auto || discriminate.
  Qed.

  Lemma step_preserves_finished_invariant :
    forall env Gamma sched_log action_log action_log_new v Gamma_new,
      interp_action env empty_sigma Gamma sched_log action_log typed_step =
        Some (action_log_new, v, Gamma_new) ->
      no_latest_writes action_log all_regs ->
      invariant (commit_update env sched_log) ->
      finished_invariant (commit_update env (log_app action_log_new sched_log)).
  Proof.
    intros.
    unfold invariant, step_invariant, finished_invariant, result_invariant in *.
    interp_action_all_t;
    Bits_to_N_t;
    intros;
    match goal with
    | [H1: ?x = ?y, H2: ?x = ?z |- _ ] => rewrite H1 in H2; discriminate H2
    end.
  Qed.

  Lemma step_preserves_step_invariant :
    forall env Gamma sched_log action_log action_log_new v Gamma_new,
      interp_action env empty_sigma Gamma sched_log action_log typed_step =
        Some (action_log_new, v, Gamma_new) ->
      no_latest_writes action_log all_regs ->
      invariant (commit_update env sched_log) ->
      step_invariant (commit_update env (log_app action_log_new sched_log)).
  Proof.
    intros.
    unfold invariant, step_invariant, finished_invariant, result_invariant in *.
    interp_action_all_t;
    Bits_to_N_t; try (assumption);
    rewrite Bits.to_N_of_N_lt;
    lia_bits.
  Qed.

  Lemma step_preserves_result_invariant :
    forall env Gamma sched_log action_log action_log_new v Gamma_new,
      interp_action env empty_sigma Gamma sched_log action_log typed_step =
        Some (action_log_new, v, Gamma_new) ->
      no_latest_writes action_log all_regs ->
      no_latest_writes sched_log all_regs ->
      invariant (commit_update env sched_log) ->
      result_invariant (commit_update env (log_app action_log_new sched_log)).
  Proof.
    intros.
    unfold invariant, step_invariant, finished_invariant, result_invariant in *.
    interp_action_all_t;
    intros;
    Bits_to_N_t;
    unfold n in *;
    try discriminate.
    match goal with
    | [ H: context[_ = partial_mul _ _ _] |- _ ] =>
      setoid_rewrite H; try assumption
    end; cbn in *.
    - rewrite Bits.to_N_of_N_lt.
      + rewrite Bits.to_N_of_N_lt by lia_bits.
        cbn. rewrite_all_hypotheses. cbn.
        rewrite N.add_1_r.
        rewrite partial_mul_step.
        rewrite_all_hypotheses.
        f_equal. cbn [N.b2n].
        rewrite N.mod_small. ring.
        assert (2 ^ 32 * 2 ^ 32 = 18446744073709551616)%N as Hdouble32 by reflexivity.
        rewrite <-Hdouble32.
        apply N.mul_lt_mono.
        * lia_bits.
        * apply N.pow_lt_mono_r; lia_bits.
      + unfold partial_mul.
        assert (2 ^ 63 + 2 ^ 63 = 18446744073709551616)%N as Hdouble63 by reflexivity.
        cbn. rewrite <-Hdouble63 at -1.
        assert (2 ^ 32 * 2 ^ 31 = 2 ^ 63)%N as H2pow3231 by reflexivity.
        rewrite <-H2pow3231.
        pose_bits_bound_proofs.
        remember_bits_to_N.
        apply N.add_lt_le_mono.
        * apply N.mul_lt_mono.
          -- lia_bits.
          -- eapply N.lt_le_trans.
             ++ apply N.mod_lt.
               match goal with
               | [ |- context[(2 ^ ?x)%N] ] => destruct x; discriminate
               end.
             ++ apply N.pow_le_mono_r; lia_bits.
        * eapply N.le_trans.
          -- apply N.mod_le. discriminate.
          -- apply N.mul_le_mono.
             ++ lia_bits.
             ++ apply N.pow_le_mono_r; lia_bits.
    - rewrite Bits.to_N_of_N_lt by lia_bits.
      cbn. rewrite N.add_1_r.
      rewrite partial_mul_step.
      setoid_rewrite_all_hypotheses. cbn.
      rewrite N.mul_0_r. rewrite N.add_0_r.
      auto.
  Qed.

  Lemma step_preserves_result_finished_invariant :
    forall env Gamma sched_log action_log action_log_new v Gamma_new,
      interp_action env empty_sigma Gamma sched_log action_log typed_step =
        Some (action_log_new, v, Gamma_new) ->
      no_latest_writes action_log all_regs ->
      no_latest_writes sched_log all_regs ->
      invariant (commit_update env sched_log) ->
      result_finished_invariant (commit_update env (log_app action_log_new sched_log)).
  Proof.
    intros.
    unfold invariant, step_invariant, finished_invariant, result_invariant, result_finished_invariant in *.
    interp_action_all_t;
    intros;
    Bits_to_N_t;
    unfold n in *;
    try match goal with
        | [ H1: ?x = ?y, H2: ?x = ?z |- _ ] =>
          rewrite H1 in H2; discriminate H2
        end;
    match goal with
    | [ H: context[_ = partial_mul _ _ _] |- _ ] =>
      setoid_rewrite H; try assumption
    end;
    cbn in *.
    - rewrite_all_hypotheses.
      rewrite Bits.to_N_of_N_lt.
      + rewrite N.mod_small by lia_bits.
        rewrite (mul_to_partial_mul (N.of_nat n) (Bits.to_N _) (Bits.to_N _)) by lia_bits.
        cbn.
        assert (32 = 31 + 1)%N as H32S by reflexivity.
        rewrite H32S.
        rewrite N.add_1_r, partial_mul_step.
        repeat (f_equal; []).
        match goal with
        | [ H1: ?x = ?y, H2: context[N.testbit _ _] |- _ ] =>
          rewrite H1 in H2
        end.
        rewrite_all_hypotheses.
        reflexivity.
      + unfold partial_mul.
        assert (2 ^ 63 + 2 ^ 63 = 18446744073709551616)%N as Hdouble63 by reflexivity.
        cbn. rewrite <-Hdouble63 at -1.
        assert (2 ^ 32 * 2 ^ 31 = 2 ^ 63)%N as H2pow3231 by reflexivity.
        rewrite <-H2pow3231.
        apply N.add_lt_le_mono.
        * apply N.mul_lt_mono; [lia_bits | ].
          apply N.mod_lt. discriminate.
        * eapply N.le_trans; [ apply N.mod_le; discriminate | ].
          apply N.mul_le_mono; lia_bits.
    - rewrite_all_hypotheses.
      rewrite (mul_to_partial_mul (N.of_nat n)) by lia_bits.
      cbn.
      assert (32 = 31 + 1)%N as H32S by reflexivity.
      rewrite H32S.
      rewrite N.add_1_r, partial_mul_step.
      repeat (f_equal; []).
      match goal with
      | [ H1: ?x = ?y, H2: context[N.testbit _ _] |- _ ] =>
        rewrite H1 in H2
      end.
      rewrite_all_hypotheses. cbn.
      rewrite N.mul_0_r. rewrite N.add_0_r.
      reflexivity.
  Qed.

  Lemma step_preserves_invariants :
    forall env Gamma sched_log action_log action_log_new v Gamma_new,
      interp_action env empty_sigma Gamma sched_log action_log typed_step =
        Some (action_log_new, v, Gamma_new) ->
      no_latest_writes action_log all_regs ->
      no_latest_writes sched_log all_regs ->
      invariant (commit_update env sched_log) ->
      invariant (commit_update env (log_app action_log_new sched_log)).
  Proof.
    intros.
    repeat split.
    - eapply step_preserves_step_invariant; eassumption.
    - eapply step_preserves_finished_invariant; eassumption.
    - eapply step_preserves_result_invariant; eassumption.
    - eapply step_preserves_result_finished_invariant; eassumption.
  Qed.

  Lemma enq_set_operands :
    forall (env: ContextEnv.(env_t) R) Gamma sched_log action_log action_log_new v Gamma_new,
      interp_action env empty_sigma Gamma sched_log action_log typed_enq =
        Some (action_log_new, v, Gamma_new) ->
      no_latest_writes action_log [operand1; operand2] ->
      latest_write action_log_new operand1 = Some (chd Gamma) /\
      latest_write action_log_new operand2 = Some (chd (ctl Gamma)).
  Proof.
    intros.
    interp_action_all_t.
    auto.
  Qed.

  Lemma step_keep_operands :
    forall (env: ContextEnv.(env_t) R) Gamma sched_log action_log action_log_new v Gamma_new,
      interp_action env empty_sigma Gamma sched_log action_log typed_step =
        Some (action_log_new, v, Gamma_new) ->
      no_latest_writes action_log [operand1; operand2] ->
      no_latest_writes action_log_new [operand1; operand2].
  Proof.
    intros.
    interp_action_all_t;
    auto.
  Qed.

  Lemma deq_result :
    forall env Gamma sched_log action_log action_log_new v Gamma_new,
      interp_action env empty_sigma Gamma sched_log action_log typed_deq =
        Some (action_log_new, v, Gamma_new) ->
      no_latest_writes action_log all_regs ->
      no_latest_writes sched_log all_regs ->
      invariant (commit_update env sched_log) ->
      let operand1_val := Bits.to_N (ContextEnv.(getenv) env operand1) in
      let operand2_val := Bits.to_N (ContextEnv.(getenv) env operand2) in
      (Bits.to_N v = operand1_val * operand2_val)%N.
  Proof.
    intros.
    unfold invariant, result_finished_invariant in *.
    interp_action_all_t.
    Bits_to_N_t.
    auto.
  Qed.

End MultiplierProofs.
