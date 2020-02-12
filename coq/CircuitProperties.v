(*! Circuits | Lemmas used in the compiler-correctness proof !*)
Require Export Koika.CircuitGeneration Koika.CircuitOptimization.
Require Import Koika.Common Koika.Environments Koika.Types Koika.Lowering.

Section Bools.
  Definition bool_le b1 b2 :=
    b2 = false ->
    b1 = false.

  Lemma bool_le_impl b1 b2 :
    bool_le b1 b2 <-> (orb (negb b1) b2) = true.
  Proof.
    destruct b1, b2; unfold bool_le; cbn; intuition.
  Qed.

  Lemma bool_le_and :
    forall b1 b1' b2 b2',
      bool_le b1 b1' ->
      bool_le b2 b2' ->
      bool_le (andb b1 b2) (andb b1' b2').
  Proof.
    unfold bool_le; intros.
    destruct b1, b2, b1', b2'; cbn;
      intuition discriminate.
  Qed.

  Lemma bool_le_and_l :
    forall b1 b1' b2,
      bool_le b1 b1' ->
      bool_le (andb b1 b2) b1'.
  Proof.
    unfold bool_le; intros.
    destruct b1, b2, b1'; cbn;
      intuition discriminate.
  Qed.

  Lemma bool_le_or :
    forall b1 b1' b2 b2',
      bool_le b1 b1' ->
      bool_le b2 b2' ->
      bool_le (orb b1 b2) (orb b1' b2').
  Proof.
    unfold bool_le; intros.
    destruct b1, b2, b1', b2'; cbn;
      intuition discriminate.
  Qed.

  Lemma bool_le_mux :
    forall (s: bool) b1 b1' b2 b2',
      bool_le b1 b1' ->
      bool_le b2 b2' ->
      bool_le (if s then b1 else b2) (if s then b1' else b2').
  Proof.
    unfold bool_le; intros.
    destruct s; cbn;
      intuition discriminate.
  Qed.

  Lemma bool_le_not :
    forall b1 b2,
      bool_le b1 b2 ->
      bool_le (negb b2) (negb b1).
  Proof.
    unfold bool_le; intros.
    destruct b1, b2; cbn;
      intuition discriminate.
  Qed.

  Lemma bool_le_true :
    forall b, bool_le b true.
  Proof.
    unfold bool_le; intros;
      destruct b; intuition discriminate.
  Qed.

  Lemma bool_le_false :
    forall b, bool_le false b.
  Proof.
    unfold bool_le; intros;
      destruct b; intuition discriminate.
  Qed.
End Bools.

Section Circuits.
  Context {pos_t var_t rule_name_t reg_t ext_fn_t: Type}.

  Context {CR: reg_t -> nat}.
  Context {CSigma: ext_fn_t -> CExternalSignature}.

  Context {REnv: Env reg_t}.
  Context (cr: REnv.(env_t) (fun idx => bits (CR idx))).

  Context {Show_rule_name_t : Show rule_name_t}.

  Context (csigma: forall f, CSig_denote (CSigma f)).
  Context (lco: (@local_circuit_optimizer
                   rule_name_t reg_t ext_fn_t CR CSigma
                   (rwdata (rule_name_t := rule_name_t) CR CSigma)
                   csigma)).

  Notation circuit := (circuit (rule_name_t := rule_name_t)
                              (rwdata := rwdata (rule_name_t := rule_name_t) CR CSigma)
                              CR CSigma).
  Notation interp_circuit := (interp_circuit cr csigma).

  Definition circuit_le (c1 c2: circuit 1) :=
    bool_le (Bits.single (interp_circuit c1)) (Bits.single (interp_circuit c2)).

  Lemma interp_circuit_circuit_le_helper_false :
    forall c1 c2,
      circuit_le c1 c2 ->
      interp_circuit c2 = Ob~0 ->
      interp_circuit c1 = Ob~0.
  Proof.
    unfold circuit_le; intros * Hlt Heq;
      destruct (interp_circuit c1) as (? & [ ]), (interp_circuit c2) as (? & []).
    inversion Heq; cbv; f_equal; apply Hlt; cbn; congruence.
  Qed.

  Lemma interp_circuit_circuit_le_helper_true :
    forall c1 c2,
      circuit_le c1 c2 ->
      interp_circuit c1 = Ob~1 ->
      interp_circuit c2 = Ob~1.
  Proof.
    unfold circuit_le; intros * Hlt Heq;
      destruct (interp_circuit c1) as (? & [ ]), (interp_circuit c2) as ([ | ] & []);
      inversion Heq; subst; cbv; f_equal; symmetry; apply Hlt; cbn; congruence.
  Qed.

  Lemma circuit_le_CAnnot :
    forall s c1 c2,
      circuit_le c1 c2 ->
      circuit_le (CAnnot s c1) (CAnnot s c2).
  Proof. firstorder. Qed.

  Lemma circuit_le_CAnnot_l :
    forall s c1 c2,
      circuit_le c1 c2 ->
      circuit_le (CAnnot s c1) c2.
  Proof. firstorder. Qed.

  Lemma circuit_le_CAnnot_r :
    forall s c1 c2,
      circuit_le c1 c2 ->
      circuit_le c1 (CAnnot s c2).
  Proof. firstorder. Qed.

  Lemma circuit_le_CBundleRef :
    forall rl1 rl2 rs1 rs2 b1 b2 field1 field2 c1 c2,
      circuit_le c1 c2 ->
      circuit_le (CBundleRef rl1 rs1 b1 field1 c1) (CBundleRef rl2 rs2 b2 field2 c2).
  Proof. firstorder. Qed.

  Lemma circuit_le_CBundleRef_l :
    forall rl1 rs1 b1 field1 c1 c2,
      circuit_le c1 c2 ->
      circuit_le (CBundleRef rl1 rs1 b1 field1 c1) c2.
  Proof. firstorder. Qed.

  Lemma circuit_le_CBundleRef_r :
    forall rl2 rs2 b2 field2 c1 c2,
      circuit_le c1 c2 ->
      circuit_le c1 (CBundleRef rl2 rs2 b2 field2 c2).
  Proof. firstorder. Qed.

  Lemma circuit_le_CAnd :
    forall c1 c1' c2 c2',
      circuit_le c1 c1' ->
      circuit_le c2 c2' ->
      circuit_le (CAnd c1 c2) (CAnd c1' c2').
  Proof. unfold circuit_le; cbn; eauto using bool_le_and. Qed.

  Lemma circuit_le_CAnd_l :
    forall c1 c1' c2,
      circuit_le c1 c1' ->
      circuit_le (CAnd c1 c2) c1'.
  Proof. unfold circuit_le; cbn; eauto using bool_le_and_l. Qed.

  Lemma circuit_le_CAnd_r :
    forall c1 c1' c2',
      circuit_le c1 c1' ->
      interp_circuit c2' = Ob~1 ->
      circuit_le c1 (CAnd c1' c2').
  Proof. unfold circuit_le; cbn. intros * ? ->.
     cbn; rewrite Bool.andb_true_r; eauto. Qed.

  Lemma circuit_le_COr :
    forall c1 c1' c2 c2',
      circuit_le c1 c1' ->
      circuit_le c2 c2' ->
      circuit_le (COr c1 c2) (COr c1' c2').
  Proof. unfold circuit_le; cbn; eauto using bool_le_or. Qed.

  Lemma circuit_le_CMux :
    forall s c1 c1' c2 c2',
      circuit_le c1 c1' ->
      circuit_le c2 c2' ->
      circuit_le (CMux s c1 c2) (CMux s c1' c2').
  Proof.
    unfold circuit_le; cbn;
      intros; destruct (Bits.single (interp_circuit s)); eauto.
  Qed.

  Lemma circuit_le_CMux_l :
    forall s c1 c2 c3,
      (interp_circuit s = Ob~1 -> circuit_le c1 c3) ->
      (interp_circuit s = Ob~0 -> circuit_le c2 c3) ->
      circuit_le (CMux s c1 c2) c3.
  Proof.
    unfold circuit_le; cbn;
      intros * Heq1 Heq2; destruct (interp_circuit s) as [ b [] ]; cbn.
    destruct b; eauto.
  Qed.

  Lemma circuit_le_CMux_r :
    forall s c1 c2 c3,
      (interp_circuit s = Ob~1 -> circuit_le c1 c2) ->
      (interp_circuit s = Ob~0 -> circuit_le c1 c3) ->
      circuit_le c1 (CMux s c2 c3).
  Proof.
    unfold circuit_le; cbn;
      intros * Heq1 Heq2; destruct (interp_circuit s) as [ b [] ]; cbn.
    destruct b; eauto.
  Qed.

  Lemma circuit_le_CNot :
    forall c1 c2,
      circuit_le c1 c2 ->
      circuit_le (CNot c2) (CNot c1).
  Proof. unfold circuit_le; cbn; eauto using bool_le_not. Qed.

  Lemma circuit_le_true :
    forall c, circuit_le c (CConst Ob~1).
  Proof. unfold circuit_le; cbn; eauto using bool_le_true. Qed.

  Lemma circuit_le_false :
    forall c, circuit_le (CConst Ob~0) c.
  Proof. unfold circuit_le; cbn; eauto using bool_le_false. Qed.

  Lemma circuit_le_fold_right {X} :
    forall (xs: list X) f0 f1 c0 c1,
      circuit_le c1 c0 ->
      (forall x acc1 acc0, circuit_le acc1 acc0 -> circuit_le (f1 x acc1) (f0 x acc0)) ->
      circuit_le (List.fold_right f1 c1 xs) (List.fold_right f0 c0 xs).
  Proof.
    induction xs; cbn; intros * Hlt Hxlt; eauto.
  Qed.

  Lemma circuit_le_refl :
    forall c, circuit_le c c.
  Proof. firstorder. Qed.

  Lemma circuit_le_trans :
    forall c1 c2 c3,
      circuit_le c1 c2 ->
      circuit_le c2 c3 ->
      circuit_le c1 c3.
  Proof. firstorder. Qed.

  Lemma circuit_le_opt_l :
    forall c1 c2,
      circuit_le c1 c2 ->
      circuit_le (lco.(lco_fn) c1) c2.
  Proof.
    unfold circuit_le; intros; rewrite lco.(lco_proof); assumption.
  Qed.

  Lemma circuit_le_opt_r :
    forall c1 c2,
      circuit_le c1 c2 ->
      circuit_le c1 (lco.(lco_fn) c2).
  Proof.
    unfold circuit_le; intros; rewrite lco.(lco_proof); assumption.
  Qed.

  Lemma circuit_le_willFire_of_canFire_canFire :
    forall rl_name c1 (cLog: scheduler_circuit (rule_name_t := rule_name_t) CR CSigma REnv) rws,
      circuit_le (willFire_of_canFire lco rl_name {| canFire := c1; regs := rws |} cLog) c1.
  Proof.
    unfold willFire_of_canFire; intros.
    eapply circuit_le_trans.
    - eapply circuit_le_fold_right.
      + apply circuit_le_refl.
      + intros; rewrite !getenv_zip.
        eapply circuit_le_opt_l, circuit_le_CAnd.
        * eassumption.
        * apply circuit_le_true.
    - cbn.
      induction finite_elements; cbn.
      + apply circuit_le_CAnnot_l, circuit_le_refl.
      + apply circuit_le_CAnd_l; eassumption.
  Qed.
End Circuits.

Ltac circuit_le_f_equal :=
  repeat (apply circuit_le_CAnnot_l ||
          apply circuit_le_CAnnot_r ||
          apply circuit_le_opt_l ||
          apply circuit_le_opt_r ||
          apply circuit_le_CBundleRef_l ||
          apply circuit_le_CBundleRef_r ||
          apply circuit_le_CAnd ||
          apply circuit_le_COr ||
          apply circuit_le_CNot ||
          apply circuit_le_true ||
          apply circuit_le_false ||
          apply circuit_le_refl).
