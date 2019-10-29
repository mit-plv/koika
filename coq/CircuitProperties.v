Require Export Coq.Bool.Bool Coq.Lists.List.
Require Export SGA.Circuits.
Require Import SGA.Common SGA.Environments SGA.Types.

Section Bools.
  Definition bool_lt b1 b2 :=
    b2 = false ->
    b1 = false.

  Lemma bool_lt_impl b1 b2 :
    bool_lt b1 b2 <-> (orb (negb b1) b2) = true.
  Proof.
    destruct b1, b2; unfold bool_lt; cbn; intuition.
  Qed.

  Lemma bool_lt_and :
    forall b1 b1' b2 b2',
      bool_lt b1 b1' ->
      bool_lt b2 b2' ->
      bool_lt (andb b1 b2) (andb b1' b2').
  Proof.
    unfold bool_lt; intros.
    destruct b1, b2, b1', b2'; cbn;
      intuition discriminate.
  Qed.

  Lemma bool_lt_and_l :
    forall b1 b1' b2,
      bool_lt b1 b1' ->
      bool_lt (andb b1 b2) b1'.
  Proof.
    unfold bool_lt; intros.
    destruct b1, b2, b1'; cbn;
      intuition discriminate.
  Qed.

  Lemma bool_lt_or :
    forall b1 b1' b2 b2',
      bool_lt b1 b1' ->
      bool_lt b2 b2' ->
      bool_lt (orb b1 b2) (orb b1' b2').
  Proof.
    unfold bool_lt; intros.
    destruct b1, b2, b1', b2'; cbn;
      intuition discriminate.
  Qed.

  Lemma bool_lt_mux :
    forall (s: bool) b1 b1' b2 b2',
      bool_lt b1 b1' ->
      bool_lt b2 b2' ->
      bool_lt (if s then b1 else b2) (if s then b1' else b2').
  Proof.
    unfold bool_lt; intros.
    destruct s; cbn;
      intuition discriminate.
  Qed.

  Lemma bool_lt_not :
    forall b1 b2,
      bool_lt b1 b2 ->
      bool_lt (negb b2) (negb b1).
  Proof.
    unfold bool_lt; intros.
    destruct b1, b2; cbn;
      intuition discriminate.
  Qed.

  Lemma bool_lt_true :
    forall b, bool_lt b true.
  Proof.
    unfold bool_lt; intros;
      destruct b; intuition discriminate.
  Qed.

  Lemma bool_lt_false :
    forall b, bool_lt false b.
  Proof.
    unfold bool_lt; intros;
      destruct b; intuition discriminate.
  Qed.
End Bools.

Section Circuits.
  Context {pos_t var_t rule_name_t reg_t ext_fn_t: Type}.

  Context {R: reg_t -> type}.
  Notation CR := (CR_of_R R).

  Context {Sigma: ext_fn_t -> ExternalSignature}.
  Notation CSigma := (CSigma_of_Sigma Sigma).

  Context {REnv: Env reg_t}.
  Context (r: REnv.(env_t) R).
  Notation cr := (cr_of_r r).

  Definition csigma_spec (sigma: forall f, Sig_denote (Sigma f)) csigma :=
    forall fn (a: (Sigma fn).(arg1Type)),
      csigma fn (bits_of_value a) = bits_of_value (sigma fn a).

  Lemma csigma_spec_csigma_of_sigma :
    forall (sigma: forall f, Sig_denote (Sigma f)),
      csigma_spec sigma (csigma_of_sigma sigma).
  Proof.
    unfold csigma_spec, csigma_of_sigma.
    intros; rewrite !value_of_bits_of_value.
    reflexivity.
  Qed.

  Context (csigma: forall f, CSig_denote (CSigma f)).
  Context (lco: (@local_circuit_optimizer
                   rule_name_t reg_t ext_fn_t CR CSigma
                   (rwdata (rule_name_t := rule_name_t) R Sigma)
                   csigma)).

  Notation circuit := (circuit (rule_name_t := rule_name_t)
                              (rwdata := rwdata (rule_name_t := rule_name_t) R Sigma)
                              CR CSigma).
  Notation interp_circuit := (interp_circuit cr csigma).

  Definition circuit_lt (c1 c2: circuit 1) :=
    bool_lt (Bits.single (interp_circuit c1)) (Bits.single (interp_circuit c2)).

  Lemma interp_circuit_circuit_lt_helper_false :
    forall c1 c2,
      circuit_lt c1 c2 ->
      interp_circuit c2 = Ob~0 ->
      interp_circuit c1 = Ob~0.
  Proof.
    unfold circuit_lt; intros * Hlt Heq;
      destruct (interp_circuit c1) as (? & [ ]), (interp_circuit c2) as (? & []).
    inversion Heq; cbv; f_equal; apply Hlt; cbn; congruence.
  Qed.

  Lemma interp_circuit_circuit_lt_helper_true :
    forall c1 c2,
      circuit_lt c1 c2 ->
      interp_circuit c1 = Ob~1 ->
      interp_circuit c2 = Ob~1.
  Proof.
    unfold circuit_lt; intros * Hlt Heq;
      destruct (interp_circuit c1) as (? & [ ]), (interp_circuit c2) as ([ | ] & []);
      inversion Heq; subst; cbv; f_equal; symmetry; apply Hlt; cbn; congruence.
  Qed.

  Lemma circuit_lt_CAnnot :
    forall s c1 c2,
      circuit_lt c1 c2 ->
      circuit_lt (CAnnot s c1) (CAnnot s c2).
  Proof. firstorder. Qed.

  Lemma circuit_lt_CAnnot_l :
    forall s c1 c2,
      circuit_lt c1 c2 ->
      circuit_lt (CAnnot s c1) c2.
  Proof. firstorder. Qed.

  Lemma circuit_lt_CAnnot_r :
    forall s c1 c2,
      circuit_lt c1 c2 ->
      circuit_lt c1 (CAnnot s c2).
  Proof. firstorder. Qed.

  Lemma circuit_lt_CBundleRef :
    forall rl1 rl2 rs1 rs2 b1 b2 field1 field2 c1 c2,
      circuit_lt c1 c2 ->
      circuit_lt (CBundleRef rl1 rs1 b1 field1 c1) (CBundleRef rl2 rs2 b2 field2 c2).
  Proof. firstorder. Qed.

  Lemma circuit_lt_CBundleRef_l :
    forall rl1 rs1 b1 field1 c1 c2,
      circuit_lt c1 c2 ->
      circuit_lt (CBundleRef rl1 rs1 b1 field1 c1) c2.
  Proof. firstorder. Qed.

  Lemma circuit_lt_CBundleRef_r :
    forall rl2 rs2 b2 field2 c1 c2,
      circuit_lt c1 c2 ->
      circuit_lt c1 (CBundleRef rl2 rs2 b2 field2 c2).
  Proof. firstorder. Qed.

  Lemma circuit_lt_CAnd :
    forall c1 c1' c2 c2',
      circuit_lt c1 c1' ->
      circuit_lt c2 c2' ->
      circuit_lt (CAnd c1 c2) (CAnd c1' c2').
  Proof. unfold circuit_lt; cbn; eauto using bool_lt_and. Qed.

  Lemma circuit_lt_CAnd_l :
    forall c1 c1' c2,
      circuit_lt c1 c1' ->
      circuit_lt (CAnd c1 c2) c1'.
  Proof. unfold circuit_lt; cbn; eauto using bool_lt_and_l. Qed.

  Lemma circuit_lt_CAnd_r :
    forall c1 c1' c2',
      circuit_lt c1 c1' ->
      interp_circuit c2' = Ob~1 ->
      circuit_lt c1 (CAnd c1' c2').
  Proof. unfold circuit_lt; cbn. intros * ? ->.
     cbn; rewrite Bool.andb_true_r; eauto. Qed.

  Lemma circuit_lt_COr :
    forall c1 c1' c2 c2',
      circuit_lt c1 c1' ->
      circuit_lt c2 c2' ->
      circuit_lt (COr c1 c2) (COr c1' c2').
  Proof. unfold circuit_lt; cbn; eauto using bool_lt_or. Qed.

  Lemma circuit_lt_CMux :
    forall s c1 c1' c2 c2',
      circuit_lt c1 c1' ->
      circuit_lt c2 c2' ->
      circuit_lt (CMux s c1 c2) (CMux s c1' c2').
  Proof.
    unfold circuit_lt; cbn;
      intros; destruct (Bits.single (interp_circuit s)); eauto.
  Qed.

  Lemma circuit_lt_CMux_l :
    forall s c1 c2 c3,
      (interp_circuit s = Ob~1 -> circuit_lt c1 c3) ->
      (interp_circuit s = Ob~0 -> circuit_lt c2 c3) ->
      circuit_lt (CMux s c1 c2) c3.
  Proof.
    unfold circuit_lt; cbn;
      intros * Heq1 Heq2; destruct (interp_circuit s) as [ b [] ]; cbn.
    destruct b; eauto.
  Qed.

  Lemma circuit_lt_CMux_r :
    forall s c1 c2 c3,
      (interp_circuit s = Ob~1 -> circuit_lt c1 c2) ->
      (interp_circuit s = Ob~0 -> circuit_lt c1 c3) ->
      circuit_lt c1 (CMux s c2 c3).
  Proof.
    unfold circuit_lt; cbn;
      intros * Heq1 Heq2; destruct (interp_circuit s) as [ b [] ]; cbn.
    destruct b; eauto.
  Qed.

  Lemma circuit_lt_CNot :
    forall c1 c2,
      circuit_lt c1 c2 ->
      circuit_lt (CNot c2) (CNot c1).
  Proof. unfold circuit_lt; cbn; eauto using bool_lt_not. Qed.

  Lemma circuit_lt_true :
    forall c, circuit_lt c (CConst Ob~1).
  Proof. unfold circuit_lt; cbn; eauto using bool_lt_true. Qed.

  Lemma circuit_lt_false :
    forall c, circuit_lt (CConst Ob~0) c.
  Proof. unfold circuit_lt; cbn; eauto using bool_lt_false. Qed.

  Lemma circuit_lt_fold_right {X} :
    forall (xs: list X) f0 f1 c0 c1,
      circuit_lt c1 c0 ->
      (forall x acc1 acc0, circuit_lt acc1 acc0 -> circuit_lt (f1 x acc1) (f0 x acc0)) ->
      circuit_lt (List.fold_right f1 c1 xs) (List.fold_right f0 c0 xs).
  Proof.
    induction xs; cbn; intros * Hlt Hxlt; eauto.
  Qed.

  Lemma circuit_lt_refl :
    forall c, circuit_lt c c.
  Proof. firstorder. Qed.

  Lemma circuit_lt_trans :
    forall c1 c2 c3,
      circuit_lt c1 c2 ->
      circuit_lt c2 c3 ->
      circuit_lt c1 c3.
  Proof. firstorder. Qed.

  Lemma circuit_lt_opt_l :
    forall c1 c2,
      circuit_lt c1 c2 ->
      circuit_lt (lco.(lco_fn) c1) c2.
  Proof.
    unfold circuit_lt; intros; rewrite lco.(lco_proof); assumption.
  Qed.

  Lemma circuit_lt_opt_r :
    forall c1 c2,
      circuit_lt c1 c2 ->
      circuit_lt c1 (lco.(lco_fn) c2).
  Proof.
    unfold circuit_lt; intros; rewrite lco.(lco_proof); assumption.
  Qed.

  Lemma circuit_lt_willFire_of_canFire_canFire :
    forall c1 (cLog: scheduler_circuit (rule_name_t := rule_name_t) R Sigma REnv) rws,
      circuit_lt (willFire_of_canFire lco {| canFire := c1; regs := rws |} cLog) c1.
  Proof.
    unfold willFire_of_canFire; intros.
    eapply circuit_lt_trans.
    - eapply circuit_lt_fold_right.
      + apply circuit_lt_refl.
      + intros; rewrite !getenv_zip.
        eapply circuit_lt_opt_l, circuit_lt_CAnd.
        * eassumption.
        * apply circuit_lt_true.
    - cbn.
      induction finite_elements; cbn.
      + apply circuit_lt_refl.
      + apply circuit_lt_CAnd_l; eassumption.
  Qed.
End Circuits.

Arguments csigma_spec {ext_fn_t Sigma} sigma csigma : assert.

Ltac circuit_lt_f_equal :=
  repeat (apply circuit_lt_CAnnot_l ||
          apply circuit_lt_CAnnot_r ||
          apply circuit_lt_opt_l ||
          apply circuit_lt_opt_r ||
          apply circuit_lt_CBundleRef_l ||
          apply circuit_lt_CBundleRef_r ||
          apply circuit_lt_CAnd ||
          apply circuit_lt_COr ||
          apply circuit_lt_CNot ||
          apply circuit_lt_true ||
          apply circuit_lt_false ||
          apply circuit_lt_refl).
