(*! Proof of correctness of the multiplier module !*)

Require Import Koika.Frontend Koika.Std Koika.ProgramTactics.
Require Export RV.Multiplier.

Module MultiplierProofs.
  Module Sig32 <: Multiplier_sig.
    Definition n := 32.
  End Sig32.
  Module mul32 := Multiplier Sig32.
  Import mul32.
  Import Sig32.

  Notation n := 32.

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

  Lemma partial_mul_step (a b n_step: N) :
    partial_mul a b (n_step + 1) =
    ((partial_mul a b n_step) +
     a * (N.b2n (N.testbit b n_step) * (2 ^ n_step)))%N.
  Proof.
  Admitted.

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

  (* Interpret all possible branches of an action *)
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
    rewrite Bits.to_N_of_N;
    lia_bits.
  Qed.

  (* The admitted subgoals should be handle by lia_bits *)
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
    unfold Sig32.n in *;
    try discriminate.
    match goal with
    | [ H: context[_ = partial_mul _ _ _] |- _ ] =>
      setoid_rewrite H; try assumption
    end; cbn in *.
    - rewrite Bits.to_N_of_N.
      + rewrite Bits.to_N_of_N by lia_bits.
        cbn. rewrite_all_hypotheses. cbn.
        rewrite partial_mul_step.
        rewrite_all_hypotheses.
        f_equal. cbn [N.b2n].
        admit.
      + admit.
    - rewrite Bits.to_N_of_N by lia_bits.
      rewrite partial_mul_step.
      rewrite_all_hypotheses. cbn.
      rewrite N.mul_0_r. rewrite N.add_0_r.
      auto.
  Admitted.

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
    unfold Sig32.n in *;
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
      rewrite Bits.to_N_of_N.
      + rewrite N.mod_small by lia_bits.
        rewrite (mul_to_partial_mul (N.of_nat Sig32.n) (Bits.to_N _) (Bits.to_N _)) by lia_bits.
        cbn.
        assert (32 = 31 + 1)%N as H32S by reflexivity.
        rewrite H32S.
        rewrite partial_mul_step.
        repeat (f_equal; []).
        match goal with
        | [ H1: ?x = ?y, H2: context[N.testbit _ _] |- _ ] =>
          rewrite H1 in H2
        end.
        rewrite_all_hypotheses.
        reflexivity.
      + admit.
    - rewrite_all_hypotheses.
      rewrite (mul_to_partial_mul (N.of_nat Sig32.n)) by lia_bits.
      cbn.
      assert (32 = 31 + 1)%N as H32S by reflexivity.
      rewrite H32S.
      rewrite partial_mul_step.
      repeat (f_equal; []).
      match goal with
      | [ H1: ?x = ?y, H2: context[N.testbit _ _] |- _ ] =>
        rewrite H1 in H2
      end.
      rewrite_all_hypotheses. cbn.
      rewrite N.mul_0_r. rewrite N.add_0_r.
      reflexivity.
    Admitted.

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
