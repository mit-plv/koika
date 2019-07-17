Require Import
        SGA.Common SGA.Syntax
        SGA.Semantics SGA.Circuits.

Require Import Coq.Lists.List.
Import ListNotations.

Section CompilerCorrectness.
  Context {var_t reg_t fn_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.

  Context {R: reg_t -> type}.
  Context {Sigma: fn_t -> ExternalSignature}.
  Context {REnv: Env reg_t}.
  Context (r: REnv.(env_t) R).
  Context (rc: REnv.(env_t) (fun reg => circuit R Sigma (R reg))).
  Context (sigma: forall f, Sigma f).
  Open Scope bool_scope.

  Notation Log := (Log R REnv).
  Notation circuit := (circuit R Sigma).
  Notation expr := (expr var_t R Sigma).
  Notation rule := (rule var_t R Sigma).
  Notation scheduler := (scheduler var_t R Sigma).
  Notation rule_circuit := (rule_circuit R Sigma REnv).
  Notation interp_circuit := (interp_circuit r sigma).
  Notation interp_circuit' := (interp_circuit' r sigma). (* FIXME *)

  (* Record rwdata_result sz := *)
  (*   { rread0: option (bits 1); *)
  (*     rread1: option (bits 1); *)
  (*     rwrite0: option (bits 1); *)
  (*     rwrite1: option (bits 1); *)
  (*     rdata0: option (bits sz); *)
  (*     rdata1: option (bits sz) }. *)

  Record rwdata_result sz :=
    { rread0: bits 1;
      rread1: bits 1;
      rwrite0: bits 1;
      rwrite1: bits 1;
      rdata0: bits sz;
      rdata1: bits sz }.

  Definition interp_rwdata {sz} (reg: @rwdata reg_t fn_t R Sigma sz) :=
    {| rread0 := interp_circuit' reg.(read0);
       rread1 := interp_circuit' reg.(read1);
       rwrite0 := interp_circuit' reg.(write0);
       rwrite1 := interp_circuit' reg.(write1);
       rdata0 := interp_circuit' reg.(data0);
       rdata1 := interp_circuit' reg.(data1) |}.

  Definition rwdata_of_log (l: Log) : REnv.(env_t) (fun idx => rwdata_result (R idx)).
  Admitted.

  Definition log_rwdata_consistent l r :=
    rwdata_of_log l =
    REnv.(Environments.map) (fun idx v => interp_rwdata v) r.

  (* Lemma canFire_expr_increasing {nRegs}: *)
  (*   forall {sig} (rl: rule sig) cLog (c1 c2: rule_circuit), *)
  (*     interp_circuit (willFire_of_canFire c1 cLog) = w1 false -> *)
  (*     compile_rule v cLog Gamma r c1 = Some c2 -> *)
  (*     interp_circuit (willFire_of_canFire c2 cLog) = w1 false. *)
  (* Proof. *)
  (* Admitted. *)

  (* Lemma canFire_rule_increasing {nRegs}: *)
  (*   forall {sig} (rl: rule sig) cLog (c1 c2: rule_circuit), *)
  (*     interp_circuit (willFire_of_canFire c1 cLog) = w1 false -> *)
  (*     compile_rule v cLog Gamma r c1 = Some c2 -> *)
  (*     interp_circuit (willFire_of_canFire c2 cLog) = w1 false. *)
  (* Proof. *)
  (* Admitted. *)

  (* Context (Gamma: vcontext sig). *)
  (* Definition gamma_consistent (gamma: gammaEnv.(env_t)) (Gamma: GammaEnv.(env_t)) := *)
  (*   (forall k c, getenv gamma k = Some c -> exists v, getenv Gamma k = Some v) /\ *)
  (*   (forall k v, getenv Gamma k = Some v -> exists c, getenv gamma k = Some c) /\ *)
  (*   (forall k c v, getenv Gamma k = Some v -> getenv gamma k = Some c -> retVal_consistent v (interp_circuit c)). *)

  (* Lemma gamma_consistent_putenv (gamma: gammaEnv.(env_t)) (Gamma: GammaEnv.(env_t)) : *)
  (*   forall k v c, *)
  (*     gamma_consistent gamma Gamma -> *)
  (*     retVal_consistent v (interp_circuit c) -> *)
  (*     gamma_consistent (putenv gamma k c) (putenv Gamma k v). *)
  (* Proof. *)
  (* Admitted. *)

  (* Hint Resolve gamma_consistent_putenv : circuits. *)
  (* Hint Resolve canFire_increasing : circuits. *)

  Ltac ceauto :=
    eauto with circuits.

  Definition bool_lt b1 b2 :=
    b2 = false ->
    b1 = false.

  Lemma bool_lt_impl b1 b2 :
    bool_lt b1 b2 <-> (orb (negb b1) b2) = true.
  Proof.
    destruct b1, b2; unfold bool_lt; cbn; intuition.
  Qed.

  Definition circuit_lt (c1 c2: circuit 1) :=
    bool_lt (Bits.single (interp_circuit' c1)) (Bits.single (interp_circuit' c2)).

  Lemma interp_circuit_circuit_lt_helper_false :
    forall c1 c2,
      circuit_lt c1 c2 ->
      interp_circuit' c2 = Ob~0 ->
      interp_circuit' c1 = Ob~0.
  Proof.
    unfold circuit_lt; intros * Hlt Heq;
      destruct (interp_circuit' c1) as (? & [ ]), (interp_circuit' c2) as (? & []).
    inversion Heq; cbv; f_equal; apply Hlt; cbn; congruence.
  Qed.

  Lemma interp_circuit_circuit_lt_helper_true :
    forall c1 c2,
      circuit_lt c1 c2 ->
      interp_circuit' c1 = Ob~1 ->
      interp_circuit' c2 = Ob~1.
  Proof.
    unfold circuit_lt; intros * Hlt Heq;
      destruct (interp_circuit' c1) as (? & [ ]), (interp_circuit' c2) as ([ | ] & []);
      inversion Heq; subst; intuition.
  Qed.

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
      interp_circuit' c2' = Ob~1 ->
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
      intros; destruct (Bits.single (interp_circuit' s)); eauto.
  Qed.

  Lemma circuit_lt_CMux_l :
    forall s c1 c2 c3,
      (interp_circuit' s = Ob~1 -> circuit_lt c1 c3) ->
      (interp_circuit' s = Ob~0 -> circuit_lt c2 c3) ->
      circuit_lt (CMux s c1 c2) c3.
  Proof.
    unfold circuit_lt; cbn;
      intros * Heq1 Heq2; destruct (interp_circuit' s) as [ b [] ]; cbn.
    destruct b; eauto.
  Qed.

  Lemma circuit_lt_CMux_r :
    forall s c1 c2 c3,
      (interp_circuit' s = Ob~1 -> circuit_lt c1 c2) ->
      (interp_circuit' s = Ob~0 -> circuit_lt c1 c3) ->
      circuit_lt c1 (CMux s c2 c3).
  Proof.
    unfold circuit_lt; cbn;
      intros * Heq1 Heq2; destruct (interp_circuit' s) as [ b [] ]; cbn.
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

  Lemma circuit_lt_willFire_of_canFire_canFire :
    forall c1 (cLog: scheduler_circuit R Sigma REnv) rws,
      circuit_lt (willFire_of_canFire {| canFire := c1; regs := rws |} cLog) c1.
  Proof.
    unfold willFire_of_canFire; intros.
    eapply circuit_lt_trans.
    - eapply circuit_lt_fold_right.
      + apply circuit_lt_refl.
      + intros; rewrite !getenv_zip.
        eapply circuit_lt_CAnd.
        * eassumption.
        * apply circuit_lt_true.
    - cbn.
      induction finite_elems; cbn.
      + apply circuit_lt_refl.
      + apply circuit_lt_CAnd_l; eassumption.
  Qed.

  Definition rwdata_circuit_lt_invariant {idx} (rwd1 rwd2: rwdata R Sigma (R idx)) :=
      circuit_lt (rwd1.(read0)) (rwd2.(read0)) /\
      circuit_lt (rwd1.(write0)) (rwd2.(write0)) /\
      circuit_lt (rwd1.(read1)) (rwd2.(read1)) /\
      circuit_lt (rwd1.(write1)) (rwd2.(write1)).

  Definition rwset_circuit_lt_invariant (rws1 rws2: rwset) idx :=
    rwdata_circuit_lt_invariant
      (REnv.(getenv) rws1 idx)
      (REnv.(getenv) rws2 idx).

  Lemma rwset_circuit_lt_invariant_refl :
    forall rws idx, rwset_circuit_lt_invariant rws rws idx.
  Proof. firstorder using circuit_lt_refl. Qed.

  Lemma rwset_circuit_lt_invariant_trans :
    forall rws1 rws2 rws3 idx,
      rwset_circuit_lt_invariant rws1 rws2 idx ->
      rwset_circuit_lt_invariant rws2 rws3 idx ->
      rwset_circuit_lt_invariant rws1 rws3 idx.
  Proof. firstorder using circuit_lt_trans. Qed.


  Lemma rwset_circuit_lt_invariant_putenv_eq :
    forall rws1 rws2 idx rwd0,
    rwdata_circuit_lt_invariant (REnv.(getenv) rws1 idx) rwd0 ->
    rwset_circuit_lt_invariant rws1 (REnv.(putenv) rws2 idx rwd0) idx.
  Proof.
    unfold rwset_circuit_lt_invariant; intros.
    rewrite get_put_eq; eauto.
  Qed.

  Lemma rwset_circuit_lt_invariant_putenv_neq :
    forall rws1 rws2 idx idx0 rwd0,
      idx <> idx0 ->
      rwset_circuit_lt_invariant rws1 rws2 idx ->
      rwset_circuit_lt_invariant rws1 (REnv.(putenv) rws2 idx0 rwd0) idx.
  Proof.
    unfold rwset_circuit_lt_invariant; intros.
    rewrite get_put_neq; eauto.
  Qed.

  Lemma rwset_circuit_lt_invariant_putenv :
    forall rws1 rws2 idx0 rwd0,
      (forall idx, rwset_circuit_lt_invariant rws1 rws2 idx) ->
      rwdata_circuit_lt_invariant (getenv REnv rws1 idx0) rwd0 ->
      (forall idx, rwset_circuit_lt_invariant rws1 (REnv.(putenv) rws2 idx0 rwd0) idx).
  Proof.
    intros.
    destruct (eq_dec idx0 idx); subst;
      eauto using rwset_circuit_lt_invariant_putenv_eq, rwset_circuit_lt_invariant_putenv_neq.
  Qed.

  Lemma rwdata_circuit_lt_invariant_mux_rwdata_l :
    forall c idx rwd1 rwd2 rwd3,
      (interp_circuit' c = Ob~1 -> @rwdata_circuit_lt_invariant idx rwd1 rwd3) ->
      (interp_circuit' c = Ob~0 -> @rwdata_circuit_lt_invariant idx rwd2 rwd3) ->
      @rwdata_circuit_lt_invariant idx (mux_rwdata c rwd1 rwd2) rwd3.
  Proof.
    unfold rwdata_circuit_lt_invariant, mux_rwdata; cbn; intros.
    repeat split; apply circuit_lt_CMux_l; intuition eauto.
  Qed.

  Lemma rwdata_circuit_lt_invariant_mux_rwdata_r :
    forall c idx rwd1 rwd2 rwd3,
      (interp_circuit' c = Ob~1 -> @rwdata_circuit_lt_invariant idx rwd1 rwd2) ->
      (interp_circuit' c = Ob~0 -> @rwdata_circuit_lt_invariant idx rwd1 rwd3) ->
      @rwdata_circuit_lt_invariant idx rwd1 (mux_rwdata c rwd2 rwd3).
  Proof.
    unfold rwdata_circuit_lt_invariant, mux_rwdata; cbn; intros.
    repeat split; apply circuit_lt_CMux_r; intuition eauto.
  Qed.

  Lemma rwset_circuit_lt_compile_expr_correct {sig tau} :
    forall (gamma : ccontext sig) (ex : expr sig tau) (rwc : rwcircuit),
      circuit_lt (canFire (erwc (compile_expr rc gamma ex rwc))) (canFire rwc) /\
      forall idx, rwset_circuit_lt_invariant (rwc.(regs)) ((compile_expr rc gamma ex rwc).(erwc).(regs)) idx.
  Proof.
    induction ex; cbn; intros; eauto using circuit_lt_refl, rwset_circuit_lt_invariant_refl.
    - destruct port; cbn.
      (* Read0 *)
      + split.
        * apply circuit_lt_CAnnot_l, circuit_lt_CAnd_l, circuit_lt_refl.
        * intros. eapply rwset_circuit_lt_invariant_putenv.
          -- eauto using rwset_circuit_lt_invariant_refl.
          -- red; cbn; eauto using circuit_lt_true, circuit_lt_refl.
      (* Read1 *)
      + split.
        * eauto using circuit_lt_refl.
        * intros; apply rwset_circuit_lt_invariant_putenv.
          -- eauto using rwset_circuit_lt_invariant_refl.
          -- red; cbn; eauto using circuit_lt_true, circuit_lt_refl.
    - specialize (IHex1 rwc);
        specialize (IHex2 (erwc (compile_expr rc gamma ex1 rwc))).
      intuition eauto using circuit_lt_trans, rwset_circuit_lt_invariant_trans.
  Qed.

  Ltac circuit_lt_f_equal :=
    repeat (apply circuit_lt_CAnnot_l ||
            apply circuit_lt_CAnnot_r ||
            apply circuit_lt_CAnd ||
            apply circuit_lt_COr ||
            apply circuit_lt_CNot ||
            apply circuit_lt_true ||
            apply circuit_lt_false ||
            apply circuit_lt_refl).

  Lemma rwset_circuit_lt_compile_rule_correct {sig}:
    forall (rl : rule sig) (gamma : ccontext sig) (rwc : rwcircuit),
      circuit_lt (canFire (compile_rule rc gamma rl rwc)) (canFire rwc) /\
      forall idx, rwset_circuit_lt_invariant (rwc.(regs)) ((compile_rule rc gamma rl rwc).(regs)) idx.
  Proof.
    induction rl; cbn; intros;
      try solve [split; circuit_lt_f_equal; eauto using rwset_circuit_lt_invariant_refl].
    - (* Seq *)
      specialize (IHrl1 gamma rwc);
        specialize (IHrl2 gamma (compile_rule rc gamma rl1 rwc)).
      intuition eauto using circuit_lt_trans, rwset_circuit_lt_invariant_trans.
    - (* Bind *)
      pose proof (rwset_circuit_lt_compile_expr_correct gamma ex rwc).
      specialize (IHrl (CtxCons (var, tau) (retVal (compile_expr rc gamma ex rwc)) gamma)
                       (erwc (compile_expr rc gamma ex rwc))).
      intuition eauto using circuit_lt_trans, rwset_circuit_lt_invariant_trans.
    - (* If *)
      pose proof (rwset_circuit_lt_compile_expr_correct gamma cond rwc).
      specialize (IHrl1 gamma (erwc (compile_expr rc gamma cond rwc))).
      specialize (IHrl2 gamma (erwc (compile_expr rc gamma cond rwc))).
      split.
      + circuit_lt_f_equal.
        apply circuit_lt_CMux_l;
          intuition eauto using circuit_lt_trans, rwset_circuit_lt_invariant_trans.
      + unfold map2; red; intros.
        rewrite getenv_create.
        apply rwdata_circuit_lt_invariant_mux_rwdata_r;
          intros; eapply rwset_circuit_lt_invariant_trans; intuition eauto.
    - (* Write *)
      pose proof (rwset_circuit_lt_compile_expr_correct gamma value rwc) as (Hpr & Hpr').
      (* destruct port; cbn. *)
      + split.
        * destruct port;
            circuit_lt_f_equal;
            apply circuit_lt_CAnd_l;
            intuition.
        * intros; destruct port;
            (apply rwset_circuit_lt_invariant_putenv;
             [ | specialize (Hpr' idx); red in Hpr' |- *; red in Hpr'; cbn;
                 repeat cleanup_step ];
             intuition eauto using circuit_lt_true).
  Qed.

  Lemma expr_compile_willFire_of_canFire'_decreasing {sig}:
    forall t (ex : expr sig t) (gamma : ccontext sig) (rwc : rwcircuit) idx rwd,
      circuit_lt (willFire_of_canFire' (getenv REnv (regs (erwc (compile_expr rc gamma ex rwc))) idx) rwd)
                 (willFire_of_canFire' (getenv REnv (regs rwc) idx) rwd).
  Proof.
    unfold willFire_of_canFire'; intros.
    pose proof (rwset_circuit_lt_compile_expr_correct gamma ex rwc) as (HCanfire & Hc);
      specialize (Hc idx); red in Hc; red in Hc; repeat cleanup_step.
    circuit_lt_f_equal; eauto.
  Qed.

  Lemma rule_compile_willFire_of_canFire'_decreasing {sig}:
    forall (rl : rule sig) (gamma : ccontext sig) (rwc : rwcircuit) idx rwd,
      circuit_lt (willFire_of_canFire' (getenv REnv (regs (compile_rule rc gamma rl rwc)) idx) rwd)
                 (willFire_of_canFire' (getenv REnv (regs rwc) idx) rwd).
  Proof.
    unfold willFire_of_canFire'; intros.
    pose proof (rwset_circuit_lt_compile_rule_correct rl gamma rwc) as (HCanfire & Hc);
      specialize (Hc idx); red in Hc; red in Hc; repeat cleanup_step.
    circuit_lt_f_equal; eauto.
  Qed.

  Lemma expr_compile_willFire_of_canFire_decreasing {sig}:
    forall t (ex : expr sig t) (cLog : scheduler_circuit R Sigma REnv)
      (gamma : ccontext sig) (rwc : rwcircuit),
      circuit_lt (willFire_of_canFire (erwc (compile_expr rc gamma ex rwc)) cLog)
                 (willFire_of_canFire rwc cLog).
  Proof.
    intros.
    unfold willFire_of_canFire.
    unfold Environments.fold_right.
    eapply circuit_lt_fold_right.
    - pose proof (rwset_circuit_lt_compile_expr_correct gamma ex rwc); intuition.
    - intros; cbn.
      rewrite !getenv_zip.
      apply circuit_lt_CAnnot_l, circuit_lt_CAnnot_r, circuit_lt_CAnd.
      + eassumption.
      + eauto using expr_compile_willFire_of_canFire'_decreasing.
  Qed.

  Lemma rule_compile_willFire_of_canFire_decreasing {sig}:
    forall (rl : rule sig) (cLog : scheduler_circuit R Sigma REnv)
      (gamma : ccontext sig) (rwc : rwcircuit),
      circuit_lt (willFire_of_canFire (compile_rule rc gamma rl rwc) cLog)
                 (willFire_of_canFire rwc cLog).
  Proof.
    intros.
    unfold willFire_of_canFire.
    unfold Environments.fold_right.
    eapply circuit_lt_fold_right.
    - pose proof (rwset_circuit_lt_compile_rule_correct rl gamma rwc); intuition.
    - intros; cbn.
      rewrite !getenv_zip.
      apply circuit_lt_CAnnot_l, circuit_lt_CAnnot_r, circuit_lt_CAnd.
      + eassumption.
      + eauto using rule_compile_willFire_of_canFire'_decreasing.
  Qed.

  Lemma willFire_of_canFire_decreasing :
    forall c1 c2 (cLog: scheduler_circuit R Sigma REnv) rws,
      circuit_lt c1 c2 ->
      circuit_lt (willFire_of_canFire {| canFire := c1; regs := rws |} cLog)
                 (willFire_of_canFire {| canFire := c2; regs := rws |} cLog).
  Proof.
    unfold willFire_of_canFire; intros.
    eapply circuit_lt_fold_right.
    - eassumption.
    - intros; rewrite !getenv_zip.
      cbn.
      eauto using circuit_lt_CAnnot_l, circuit_lt_CAnd, circuit_lt_refl.
  Qed.

  Ltac t_step :=
    match goal with
    | _ => cleanup_step
    | _ => progress intros
    | [ Heq: interp_circuit ?x = Some _ |- context[interp_circuit ?x] ] =>
      rewrite Heq
    | [ IH: context[interp_expr _ _ _ _ _ ?ex] |-
        context[interp_expr _ _ ?Gamma ?Log ?log ?ex] ] =>
      specialize (IH _ Gamma _ log ltac:(eauto) ltac:(eauto) ltac:(eauto) ltac:(eauto));
      cbv zeta in IH;
      destruct (interp_expr _ _ Gamma Log log ex) as [(? & ?) | ] eqn:?; cbn
    | [ |- match (if ?x then _ else _) with _ => _ end ] =>
      destruct x eqn:?; cbn
    | [ IH: context[interp_rule _ _ _ _ _ ?rl] |-
        context[interp_rule _ _ ?Gamma ?Log ?log ?rl] ] =>
      specialize (IH _ Gamma _ log ltac:(eauto) ltac:(eauto) ltac:(eauto) ltac:(eauto));
      cbv zeta in IH;
      destruct (interp_rule _ _ Gamma Log log rl) as [? | ] eqn:?; cbn
    end.

  (* Create HintDb circuits discriminated. *)
  Ltac t := repeat t_step; eauto.  (* with circuits. *)

  Require Import Bool.
  (* https://coq-club.inria.narkive.com/HeWqgvKm/boolean-simplification *)
  Hint Rewrite
       orb_false_r (** b || false -> b *)
       orb_false_l (** false || b -> b *)
       orb_true_r (** b || true -> true *)
       orb_true_l (** true || b -> true *)
       andb_false_r (** b && false -> false *)
       andb_false_l (** false && b -> false *)
       andb_true_r (** b && true -> b *)
       andb_true_l (** true && b -> b *)
       negb_orb (** negb (b || c) -> negb b && negb c *)
       negb_andb (** negb (b && c) -> negb b || negb c *)
       negb_involutive (** negb( (negb b) -> b *)
    : bool_simpl.
  Ltac bool_simpl := autorewrite with bool_simpl in *.

  Lemma expr_compiler_correct {sig tau} Log cLog:
    forall (ex: expr sig tau) (clog: rule_circuit)
      (Gamma: vcontext sig) (gamma: ccontext sig) log,
      log_rwdata_consistent log clog.(regs) ->
      (forall k tau' (m: member (k, tau') sig) , interp_circuit' (cassoc m gamma) = cassoc m Gamma) ->
      (forall idx, interp_circuit' (getenv REnv rc idx) = getenv REnv r idx) ->
      interp_circuit' (willFire_of_canFire clog cLog) = Ob~1 ->
      let cExpr := compile_expr rc gamma ex clog in
      match interp_expr r sigma Gamma Log log ex with
      | Some (l', v) =>
        interp_circuit' cExpr.(retVal) = v /\
        log_rwdata_consistent l' cExpr.(erwc).(regs) /\
        interp_circuit' (willFire_of_canFire cExpr.(erwc) cLog) = Ob~1
      | None =>
        interp_circuit' (willFire_of_canFire cExpr.(erwc) cLog) = Ob~0
      end.
  Proof.
    induction ex; intros.
    - (* Var *) cbn; eauto.
    - (* Const *) cbn; eauto.
    - (* Read *)
      destruct port.
      + cbn.
        destruct (may_read0 Log log idx) eqn:?; cbn.
        * repeat split.
          -- eauto.
          -- admit.
          -- eapply interp_circuit_circuit_lt_helper_true; try eassumption.
             unfold willFire_of_canFire, willFire_of_canFire'; cbn.
             apply circuit_lt_fold_right.
             ++ apply circuit_lt_CAnd_r.
                apply circuit_lt_refl.
                cbn. admit.
             ++ intros.
                rewrite !getenv_zip; cbn.
                destruct (eq_dec idx x); subst;
                  [ rewrite !get_put_eq | rewrite !get_put_neq by eassumption ];
                  cbn;
                  circuit_lt_f_equal;
                  try eassumption.
                unfold circuit_lt; cbn.
                apply bool_lt_impl.
                replace (interp_circuit' (write0 (getenv REnv (sregs cLog) x))) with Ob~0 by admit.
                replace (interp_circuit' (write1 (getenv REnv (sregs cLog) x))) with Ob~0 by admit.
                cbn; bool_simpl; reflexivity.
        * eapply interp_circuit_circuit_lt_helper_false.
          apply circuit_lt_willFire_of_canFire_canFire.
          cbn.
          cut ((interp_circuit' (read1 (getenv REnv (regs clog) idx))) = Ob~1 \/
               (interp_circuit' (write1 (getenv REnv (regs clog) idx))) = Ob~1).
          intros [-> | ->]; bool_simpl; reflexivity.
          admit.
      + cbn.
        destruct (may_read1 Log idx) eqn:?; cbn.
        * repeat split.
          -- admit. (* Log consistency property *)
          -- admit.
          -- eapply interp_circuit_circuit_lt_helper_true; try eassumption.
             unfold willFire_of_canFire, willFire_of_canFire'; cbn.
             apply circuit_lt_fold_right.
             ++ circuit_lt_f_equal.
             ++ intros.
                rewrite !getenv_zip; cbn.
                destruct (eq_dec idx x); subst;
                  [ rewrite !get_put_eq | rewrite !get_put_neq by eassumption ];
                  cbn;
                  circuit_lt_f_equal;
                  try eassumption.
                unfold circuit_lt; cbn.
                apply bool_lt_impl.
                replace (interp_circuit' (write1 (getenv REnv (sregs cLog) x))) with Ob~0 by admit.
                cbn; bool_simpl; reflexivity.
        * (* FIXME write two lemmas to focus on the changed element in regs *)
          admit. (* may_read1 = false -> there's a write1 *)
    - (* Call *)
      repeat t_step; eauto.
      eapply interp_circuit_circuit_lt_helper_false;
        eauto using expr_compile_willFire_of_canFire_decreasing.
  Admitted.

  Lemma rule_compiler_correct {sig} Log cLog:
    forall (rl: rule sig) (clog: rule_circuit)
      (Gamma: vcontext sig) (gamma: ccontext sig) log,
      log_rwdata_consistent log clog.(regs) ->
      (forall k tau' (m: member (k, tau') sig) , interp_circuit' (cassoc m gamma) = cassoc m Gamma) ->
      (forall idx, interp_circuit' (getenv REnv rc idx) = (getenv REnv r idx)) ->
      interp_circuit' (willFire_of_canFire clog cLog) = Ob~1 ->
      let cRule := compile_rule rc gamma rl clog in
      match interp_rule r sigma Gamma Log log rl with
      | Some (l') =>
        log_rwdata_consistent l' cRule.(regs) /\
        interp_circuit' (willFire_of_canFire cRule cLog) = Ob~1
      | None =>
        interp_circuit' (willFire_of_canFire cRule cLog) = Ob~0
      end.
  Proof.
    induction rl; intros; try solve[cbn; eauto].
    - (* Fail *)
      cbn; intros.
      destruct clog.
      eapply interp_circuit_circuit_lt_helper.
      + apply circuit_lt_willFire_of_canFire_canFire.
      + reflexivity.
    - (* Seq *)
      cbn.
      t.
      eapply interp_circuit_circuit_lt_helper;
        eauto using rule_compile_willFire_of_canFire_decreasing.
    - (* Bind *)
      cbn.
      pose proof (@expr_compiler_correct sig tau Log cLog ex).
      t.
      + cbn.
        (* Need lemma to be able to specialize IH despite the CtxCons *)
        (* lazymatch goal with *)
        (* | [ IH: context[interp_rule _ _ _ _ _ ?rl] |- *)
        (*     context[interp_rule _ _ ?Gamma ?Log ?log ?rl] ] => *)
        (*   specialize (fun cc => IH _ Gamma cc log ltac:(eauto) ltac:(eauto) ltac:(eauto) ltac:(eauto)); *)
        (*     cbv zeta in IH *)
        (* end. *)
        (*     destruct (interp_rule _ _ Gamma Log log rl) as [? | ] eqn:?; cbn *)
        (*             end. *)
        admit.
      + eapply interp_circuit_circuit_lt_helper;
          eauto using rule_compile_willFire_of_canFire_decreasing.
    - (* If *)
      pose proof (@expr_compiler_correct sig _ Log cLog cond).
      cbn; t.
      + split.
        admit.
        
      + destruct (Bits.single _); cbn.
        admit.                    (* WF_cF and mux lemmas *)
        admit.                    (* WF_cF and mux lemmas *)
      + admit. (* More WF decreasing, but with cmux this time. *)
    - (* Write *)
      cbn.
      t.
      pose proof (@expr_compiler_correct sig _ Log cLog value).
      t.
      + destruct (may_write Log l port idx); cbn.
        * admit.
        * admit. (* decreasing *)
      + admit. (* decreasing *)
  Admitted.

  Lemma scheduler_compiler_correct:
    forall (s: scheduler) Log cLog,
      log_rwdata_consistent Log cLog.(sregs) ->
      (forall idx, interp_circuit (getenv REnv rc idx) = Some (getenv REnv r idx)) ->
      log_rwdata_consistent
        (interp_scheduler' r sigma Log s)
        (compile_scheduler' rc s cLog).(sregs).
  Proof.
    induction s; cbn; intros.
    - eauto.
    - pose proof (@rule_compiler_correct nil Log cLog r0).
      unshelve eassert (H1 := H1 _ CtxEmpty _ log_empty ltac:(eauto) ltac:(eauto) ltac:(eauto) ltac:(eauto)).
      apply CtxEmpty.
      apply (adapter cLog).     (* Should get these from call to compile_rule *)
      cbv zeta in H1.
      destruct (interp_rule r sigma CtxEmpty Log log_empty r0); cbn; t.
      + set (fun _ => _).
        set (fun _ => _).
        set (fun _ => _).
        admit.                  (* CMuxes simplify because rule doesn't run *)
      + admit.
  Admitted.
      
      
lazymatch goal with
      | [ IH: context[interp_rule _ _ _ _ _ ?rl] |-
          context[interp_rule _ _ ?Gamma ?Log ?log ?rl] ] =>
        specialize (IH _ Gamma _ log ltac:(eauto) ltac:(eauto) ltac:(eauto) ltac:(eauto));
          cbv zeta in IH;
          destruct (interp_rule _ _ Gamma Log log rl) as [? | ] eqn:?; cbn
                  end.

      
  Ltac tstep :=
      match goal with
      | _ => cleanup_step
      | _ => progress intros

      | [ IH: (forall gamma rc, match compile_rule ?sigma ?L gamma ?r rc with _ => _ end)
          |- match opt_bind (compile_rule ?sigma ?L ?gamma ?r ?rc) _ with _ => _ end] =>
        specialize (IH gamma rc);
        destruct (compile_rule sigma L gamma r) eqn:?; cbn; ceauto; []

      | [ IH: (forall Gamma l,
                  gamma_consistent _ Gamma ->
                  log_rwdata_consistent l (regs ?rc) ->
                  interp_circuit (willFire_of_canFire ?rc _) = w1 true ->
                  match interp_rule ?R ?Sigma Gamma ?L l ?r with _ => _ end)
          |- context [interp_rule ?R ?Sigma ?Gamma ?L ?l ?r] ] =>
        specialize (IH Gamma l ltac:(ceauto) ltac:(ceauto) ltac:(ceauto));
        destruct (interp_rule R Sigma Gamma L l r) as [(? & ?) | | ] eqn:?; cbn

      | [ |- match opt_bind ?x _ with _ => _ end] =>
        destruct x eqn:?; cbn; ceauto; []

      | [ |- match result_bind (opt_result Stuck ?x) _ with _ => _ end] =>
        destruct x eqn:?; cbn; ceauto; []

      | [ |- match result_bind (bool_result ?x) _ with _ => _ end] =>
        destruct x eqn:?; cbn; ceauto; []

      | [ H: getenv ?gamma ?k = Some ?c, H': gamma_consistent ?gamma ?Gamma
          |- context[getenv ?Gamma ?k] ] =>
        pose_once (and_fst H') k c H

      | [ |- match (match ?v with _ => _ end) with _ => _ end] =>
        destruct v eqn:?; cbn; ceauto

      | [ H: retVal_consistent ?v ?bs |- context[?bs] ] =>
        rewrite H

      | [ H: ?x = ?y |- context[?x] ] =>
        let y_hd := constr_hd y in
        is_constructor y_hd; rewrite H

      | [ H: exists _, getenv _ _ = Some _ |- _ ] =>
        destruct H; try (rewrite H; cbn)

      | [  |- _ /\ _ ] => split

      | _ => progress unfold result_map
      end.

    Ltac t := repeat tstep; ceauto.

    induction rule; cbn; intros; try solve[t; ceauto].

    Opaque willFire_of_canFire.

    - t.

      + unfold log_rwdata_consistent.
        intros. erewrite Vector.nth_map2; try reflexivity.
        unfold interp_rwdata.
        cbn.
        t.
      +

        (* FIXME simplify these cases: in each case the rule is either true or false. *)
        admit.
      + unfold log_rwdata_consistent.
        intros. erewrite Vector.nth_map2; try reflexivity.
        unfold interp_rwdata.
        cbn.
        t.
      + admit.
      + unfold log_rwdata_consistent.
        intros. erewrite Vector.nth_map2; try reflexivity.
        unfold interp_rwdata.
        cbn.
        t.
      + admit.
      + admit.
      + unfold log_rwdata_consistent.
        intros. erewrite Vector.nth_map2; try reflexivity.
        unfold interp_rwdata.
        cbn.
        t.
      + admit.
      + admit.
      + unfold log_rwdata_consistent.
        intros. erewrite Vector.nth_map2; try reflexivity.
        unfold interp_rwdata.
        cbn.
        t.
      + admit.
      + admit.
      + admit.
      + admit.
      + unfold log_rwdata_consistent.
        intros. erewrite Vector.nth_map2; try reflexivity.
        unfold interp_rwdata.
        cbn.
        t.
      + admit.
      + admit.
      +
        Transparent willFire_of_canFire.

Lemma cand_true: forall bs1 bs2,
          cand bs1 bs2 = w1 true ->
          bs1 = w1 true /\ bs2 = w1 true.
        Proof. destruct bs1 as [ | [ | ] [ | ? ] ]; cbn;
             destruct bs2 as [ | [ | ] [ | ? ] ]; cbn.
           all: intros; try discriminate; eauto.
        Qed.

Arguments willFire_of_canFire' : simpl never.
  Lemma interp_willFire_of_canFire {nRegs}:
    forall cRule cInput,
      (interp_circuit (cRule.(canFire)) = w1 true /\
       Vector.Forall2 (fun ruleReg inReg =>
                         interp_circuit (willFire_of_canFire' ruleReg inReg) = w1 true)
                      cRule.(regs) cInput.(sregs)) <->
      interp_circuit (willFire_of_canFire (nRegs := nRegs) cRule cInput) = w1 true.
  Proof.
    destruct cRule, cInput; unfold rwset in *; clear R.
    revert canFire.
    cbn.
    pattern regs, sregs.
    revert regs sregs; revert nRegs.
    eapply VectorDef.rect2; cbn.
    - split; [intros (Heq & HForall) | split].
      + eauto.
      + eauto.
      + econstructor.
    - split; [intros (Heq & HForall) | ].
      + inversion HForall; subst.
        rewrite (and_fst (H canFire)), H4.
        * reflexivity.
        * Require Import Program.
          repeat simpl_existT; subst.         (* FIXME use decidable eq instead *)
          eauto.
      + intros H0.
        apply cand_true in H0; destruct H0.
        rewrite <- H in H0; destruct H0.
        split.
        * eauto.
        * econstructor; eauto.
  Qed.

  Lemma interp_willFire_of_canFire_false {nRegs}:
    forall cRule cInput,
      (interp_circuit (cRule.(canFire)) = w1 false \/
       Vector.Exists2 (fun ruleReg inReg =>
                         interp_circuit (willFire_of_canFire' ruleReg inReg) = w1 false)
                      cRule.(regs) cInput.(sregs)) <->
      interp_circuit (willFire_of_canFire (nRegs := nRegs) cRule cInput) = w1 false.
  Proof.
    destruct cRule, cInput; unfold rwset in *; clear R.
    revert canFire.
    cbn.
    pattern regs, sregs.
    revert regs sregs; revert nRegs.
    eapply VectorDef.rect2.
    - split; [intros [ Heq | HExists ] | intros ].
      + eauto.
      + inversion HExists.
      + eauto.
    - cbn; split; [intros  [ Heq | HExists ] | intros ].
      + rewrite (and_fst (H canFire)).
      (* Needs well-formedness to apply theorem *)
      + inversion HForall; subst.
        rewrite (and_fst (H canFire)), H4.
        * reflexivity.
        * Require Import Program.
          repeat simpl_existT; subst.         (* FIXME use decidable eq instead *)
          eauto.
      + intros H0.
        apply cand_true in H0; destruct H0.
        rewrite <- H in H0; destruct H0.
        split.
        * eauto.
        * econstructor; eauto.
  Qed.

  
  
        
                                        destruct bs
    
    revert dependent nRegs.
        
  
        
        unfold willFire_of_canFire.
        cbn.

        admit.

    (* FIMXE handle above admits with setoid rewriting? *)
    (* Better: prove that interp of fold_left2 is the same as forall_interp /\ init cond *)

    -                                              
          


      admit.

    - t.

      + lazymatch goal with
        | [ |- match result_bind (bool_result ?x) _ with _ => _ end] =>
          destruct x eqn:?; cbn; ceauto
        end.

        t.

        * admit. (* getEnv and v *)
        * admit. (* pure calculation *)
        * admit. (* may_read0 true case *)
        * admit. (* may_read0 false case *)

      + lazymatch goal with
        | [ |- match result_bind (bool_result ?x) _ with _ => _ end] =>
          destruct x eqn:?; cbn; ceauto
        end.

        destruct (latest_write0 (log ++ Log)) as [ [? ? ? ?] |] eqn:?; cbn.
        replace (assert_size val (length l)) with (Success val) by admit. (* Log is consistent *)
        cbn.
        * t. (* latest_write0 *)
          -- (* Lemma: constistent ⇒ latest_write0 ⇒ data0 is set *)
            admit. (* FIXME: but this looks only at clog, not at CLog; why? *)
          -- (* add_consistent *)
            admit.
          -- (* may_read1 ⇒ guard ok *)
            admit.

        * t. (* no latest write0 *)
          -- consistent ⇒ latest_write0 none ⇒
    - tstep.
      tstep.
      tstep.
      tstep.
      tstep.
      tstep.
      tstep.
      tstep.
      tstep.
      tstep.
      tstep.
      tstep.
      tstep.
      tstep.
      tstep.
      tstep.
      tstep.
      tstep.
      tstep.

      match goal with
      | [ H: retVal_consistent ?v ?bs |- context[?bs] ] =>
        rewrite H
      end.
      tstep.
      eauto.
      tstep.
      rewrite H2.
      tstep.
      tstep.
      tstep.
      tstep.
      tstep.

      lazymatch goal with
      end.
      eapply H; eassumption.
      eapply (and_snd (and_snd H)).
      intuition ceauto.

    - tstep; ceauto.
      tstep; ceauto.
      tstep; ceauto.
      tstep; ceauto.
      tstep; ceauto.
      2: admit.                 (* cond cannot run *)
      tstep; ceauto.
      tstep; ceauto.
      tstep; ceauto.
      tstep; ceauto.
      tstep; ceauto.
      tstep; ceauto.
      2: admit.                (* Second branch of if *)
      tstep; ceauto.
      tstep; ceauto.
      tstep; ceauto.
      tstep; ceauto.
      tstep; ceauto.
      tstep; ceauto.
      tstep; ceauto.

    -

    repeat match goal with
           | _ => progress t
           end.

    repeat match goal with
           end.
    ceauto.

    erewrite H1.
    - cbn; intros.
      destruct getenv eqn:?; cbn; ceauto; [].
      intros.
      destruct (getenv Gamma var); cbn; [ | admit (* would be inconsistent with gamma *) ].
      ceauto. (* Just neet to have Some -> Some in the gammas here *)
    - cbn; intros.
      ceauto.
    - cbn; intros.
      ceauto.
    - cbn; intros.

      