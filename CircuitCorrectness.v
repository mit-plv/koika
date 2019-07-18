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

  Ltac circuit_lt_f_equal :=
    repeat (apply circuit_lt_CAnnot_l ||
            apply circuit_lt_CAnnot_r ||
            apply circuit_lt_CAnd ||
            apply circuit_lt_COr ||
            apply circuit_lt_CNot ||
            apply circuit_lt_true ||
            apply circuit_lt_false ||
            apply circuit_lt_refl).

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

  Lemma interp_willFire_of_canFire_canFire_false :
    forall (c: circuit 1) (rwd: rwset) (cLog: scheduler_circuit R Sigma REnv),
      interp_circuit' c = Ob~0 ->
      interp_circuit' (willFire_of_canFire {| canFire := c; regs := rwd |} cLog) = Ob~0.
  Proof.
    intros.
    eapply interp_circuit_circuit_lt_helper_false.
    apply circuit_lt_willFire_of_canFire_canFire.
    eassumption.
  Qed.

  (* FIXME move to common *)
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

  Lemma bits_single_bits_cons :
    forall bs,
      Bits.cons (Bits.single bs) Bits.nil = bs.
  Proof. destruct bs as [ ? [ ] ]; reflexivity. Qed.

  Lemma bits_cons_inj :
    forall {sz} b1 b2 (t1 t2: bits sz),
      Bits.cons b1 t1 = Bits.cons b2 t2 ->
      b1 = b2 /\ t1 = t2.
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Lemma bits_single_inj:
    forall bs1 bs2,
      Bits.single bs1 = Bits.single bs2 ->
      bs1 = bs2.
  Proof.
    intros * Heq; rewrite <- (bits_single_bits_cons bs1), <- (bits_single_bits_cons bs2), Heq; reflexivity.
  Qed.

  Require Import Ring_theory Ring Coq.setoid_ring.Ring.

  Lemma interp_willFire_of_canFire_eqn :
    forall clog (cLog: scheduler_circuit R Sigma REnv),
      interp_circuit' (willFire_of_canFire clog cLog) =
      Ob~(andb (Bits.single (interp_circuit' (canFire clog)))
               (List.forallb (fun idx =>
                                (Bits.single
                                   (interp_circuit'
                                      (willFire_of_canFire'
                                         (REnv.(getenv) clog.(regs) idx)
                                         (REnv.(getenv) cLog.(sregs) idx)))))
                             (finite_elems (FiniteType := finite_keys REnv)))).
  Proof.
    unfold willFire_of_canFire, Environments.fold_right; cbn.
    induction finite_elems; cbn; intros.
    - bool_simpl; rewrite bits_single_bits_cons; reflexivity.
    - rewrite getenv_zip; cbn.
      rewrite IHl; cbn.
      f_equal.
      ring.
  Qed.

  Lemma interp_willFire_of_canFire_true :
    forall clog (cLog: scheduler_circuit R Sigma REnv),
      interp_circuit' (willFire_of_canFire clog cLog) = Ob~1 <->
      interp_circuit' (canFire clog) = Ob~1 /\
      forall idx, interp_circuit'
               (willFire_of_canFire'
                  (REnv.(getenv) clog.(regs) idx)
                  (REnv.(getenv) cLog.(sregs) idx)) = Ob~1.
  Proof.
    split; intros * H.
    - rewrite interp_willFire_of_canFire_eqn in H.
      apply bits_cons_inj in H; repeat cleanup_step || bool_step.
      split.
      + eauto using bits_single_inj.
      + intros idx.
        lazymatch goal with
        | [ H: forallb _ _ = _ |- _ ] =>
          rewrite forallb_forall in H;
            specialize (H idx ltac:(eauto using member_In, finite_index))
        end.
        eauto using bits_single_inj.
    - repeat cleanup_step.
      rewrite interp_willFire_of_canFire_eqn.
      f_equal.
      apply (f_equal Bits.single) in H; cbn in H; rewrite H.
      bool_simpl.
      apply forallb_forall; intros idx **.
      rewrite H0; reflexivity.
  Qed.

  Ltac bool_step :=
    match goal with
    | [ H: andb _ _ = true |- _ ] =>
      apply andb_prop in H
    | [ H: andb _ _ = false |- _ ] =>
      rewrite andb_false_iff in H
    | [ H: orb _ _ = true |- _ ] =>
      apply orb_prop in H       (* FIXME: Added this *)
    | [ H: orb _ _ = false |- _ ] =>
      rewrite orb_false_iff in H       (* FIXME: Added this *)
    | [ H: forallb _ (_ ++ _) = _ |- _ ] =>
      rewrite forallb_app in H
    | [ H: Some _ = Some _ |- _ ] =>
      inversion H; subst; clear H
    end.

  Lemma forallb_exists {A}:
    forall f (l: list A),
      forallb f l = false <->
      exists x, List.In x l /\ f x = false.
  Proof.
    induction l; cbn; split.
    - congruence.
    - intros [x (? & ?)]; exfalso; assumption.
    - intros H; repeat bool_step; destruct H.
      + exists a; eauto.
      + firstorder.
    - intros [x [ [ ? | ? ] Hnx ] ]; subst; try rewrite Hnx.
      + reflexivity.
      + replace (forallb f l) with false by (symmetry; rewrite IHl; eauto);
          bool_simpl; reflexivity.
  Qed.

  Opaque willFire_of_canFire'.

  Lemma interp_willFire_of_canFire_false :
    forall clog (cLog: scheduler_circuit R Sigma REnv),
      interp_circuit' (willFire_of_canFire clog cLog) = Ob~0 <->
      interp_circuit' (canFire clog) = Ob~0 \/
      exists idx, interp_circuit'
               (willFire_of_canFire'
                  (REnv.(getenv) clog.(regs) idx)
                  (REnv.(getenv) cLog.(sregs) idx)) = Ob~0.
  Proof.
    split; intros * H.
    - rewrite interp_willFire_of_canFire_eqn in H.
      apply bits_cons_inj in H; repeat cleanup_step || bool_step; destruct H.
      + eauto using bits_single_inj.
      + right. rewrite forallb_exists in H.
        destruct H as (idx & _ & Heq).
        eauto using bits_single_inj.
    - rewrite interp_willFire_of_canFire_eqn; f_equal.
      rewrite andb_false_iff; destruct H as [ -> | ( idx & Heq ) ]; [left | right].
      + reflexivity.
      + rewrite forallb_exists.
        exists idx; rewrite Heq.
        eauto using member_In, finite_index.
  Qed.

  Transparent willFire_of_canFire'.

  (* Lemma interp_willFire_of_canFire_willFire'_false : *)
  (*   forall clog (cLog: scheduler_circuit R Sigma REnv) idx, *)
  (*     interp_circuit' (willFire_of_canFire' (REnv.(getenv) clog.(regs) idx) (REnv.(getenv) cLog.(sregs) idx)) = Ob~0 -> *)
  (*     interp_circuit' (willFire_of_canFire clog cLog) = Ob~0. *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold willFire_of_canFire, Environments.fold_right; cbn. *)
  (*   destruct (in_split idx finite_elems (member_In _ _ (@finite_index _ (finite_keys REnv) idx))) *)
  (*     as (l1 & l2 & ->). *)
  (*   rewrite fold_right_app; cbn. *)
  (*   rewrite !getenv_zip; cbn. *)
  (*   apply circuit_lt_fold_right. *)
  (*   - apply circuit_lt_refl. *)
  (*   - intros idx' ** ; *)
  (*       rewrite getenv_zip; *)
  (*       destruct (eq_dec idx' idx); subst. *)
  (*     + lazymatch goal with *)
  (*       | [ H: circuit_lt ?x ?y |- circuit_lt ?c1 (?f ?idx ?y) ] => *)
  (*         let cc := (eval pattern idx, x in c1) in *)
  (*         let cchd := constr_hd cc in *)
  (*         unify (f idx y) (cchd idx y); *)
  (*           cbn *)
  (*       end. *)
  (*       circuit_lt_f_equal; eassumption. *)
  (*     + cbn. *)
  (*       circuit_lt_f_equal; eassumption. *)
  (*   -  *)
  (* Qed. *)

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

  Lemma circuit_lt_willFire_of_canFire':
    forall idx (rwd0 rwd1 rwd2: rwdata R Sigma (R idx)),
      rwdata_circuit_lt_invariant rwd1 rwd0 ->
      circuit_lt (willFire_of_canFire' rwd0 rwd2) (willFire_of_canFire' rwd1 rwd2).
  Proof.
    unfold rwdata_circuit_lt_invariant; intros; repeat cleanup_step; circuit_lt_f_equal;
      eauto.
  Qed.

  Lemma circuit_lt_willFire_of_canFire :
    forall (l1 l2: rule_circuit) L,
      circuit_lt (canFire l1) (canFire l2) ->
      (forall idx, rwset_circuit_lt_invariant l2.(regs) l1.(regs) idx) ->
      circuit_lt (willFire_of_canFire l1 L) (willFire_of_canFire l2 L).
  Proof.
    unfold willFire_of_canFire; intros * Hlt Hfr.
    apply circuit_lt_fold_right.
    - eassumption.
    - intros; rewrite !getenv_zip; cbn.
      apply circuit_lt_CAnd.
      assumption.
      apply circuit_lt_willFire_of_canFire'.
      apply Hfr.
  Qed.

  Lemma expr_compile_willFire_of_canFire'_decreasing {sig}:
    forall t (ex : expr sig t) (gamma : ccontext sig) (rwc : rwcircuit) idx rwd,
      circuit_lt (willFire_of_canFire' (getenv REnv (regs (erwc (compile_expr rc gamma ex rwc))) idx) rwd)
                 (willFire_of_canFire' (getenv REnv (regs rwc) idx) rwd).
  Proof.
    intros; apply circuit_lt_willFire_of_canFire';
      pose proof (rwset_circuit_lt_compile_expr_correct gamma ex rwc) as (H & H'); red in H'; intuition.
  Qed.

  Lemma rule_compile_willFire_of_canFire'_decreasing {sig}:
    forall (rl : rule sig) (gamma : ccontext sig) (rwc : rwcircuit) idx rwd,
      circuit_lt (willFire_of_canFire' (getenv REnv (regs (compile_rule rc gamma rl rwc)) idx) rwd)
                 (willFire_of_canFire' (getenv REnv (regs rwc) idx) rwd).
  Proof.
    intros; apply circuit_lt_willFire_of_canFire';
      pose proof (rwset_circuit_lt_compile_rule_correct rl gamma rwc) as (H & H'); red in H'; intuition.
  Qed.

  Lemma expr_compile_willFire_of_canFire_decreasing {sig}:
    forall t (ex : expr sig t) (cLog : scheduler_circuit R Sigma REnv)
      (gamma : ccontext sig) (rwc : rwcircuit),
      circuit_lt (willFire_of_canFire (erwc (compile_expr rc gamma ex rwc)) cLog)
                 (willFire_of_canFire rwc cLog).
  Proof.
    intros; apply circuit_lt_willFire_of_canFire;
      pose proof (rwset_circuit_lt_compile_expr_correct gamma ex rwc); intuition.
  Qed.

  Lemma rule_compile_willFire_of_canFire_decreasing {sig}:
    forall (rl : rule sig) (cLog : scheduler_circuit R Sigma REnv)
      (gamma : ccontext sig) (rwc : rwcircuit),
      circuit_lt (willFire_of_canFire (compile_rule rc gamma rl rwc) cLog)
                 (willFire_of_canFire rwc cLog).
  Proof.
    intros; apply circuit_lt_willFire_of_canFire;
      pose proof (rwset_circuit_lt_compile_rule_correct rl gamma rwc); intuition.
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

  Context {var_t_eq_dec: EqDec var_t}.

  Definition circuit_gamma_equiv {sig} (Gamma : vcontext sig) (gamma : ccontext sig) :=
    (forall (k: var_t) tau (m : member (k, tau) sig),
        interp_circuit' (cassoc m gamma) = cassoc m Gamma).

  Lemma circuit_gamma_equiv_CtxCons {sig}:
    forall Gamma gamma,
      circuit_gamma_equiv (Gamma: vcontext sig) (gamma: ccontext sig) ->
      forall (tau : type) (var : var_t) (c : circuit tau),
        circuit_gamma_equiv (CtxCons (var, tau) (interp_circuit' c) Gamma) (CtxCons (var, tau) c gamma).
  Proof.
    unfold circuit_gamma_equiv; intros.
    destruct (mdestruct m) as [(? & ->) | (m' & ->)]; cbn.
    - inversion x; subst.
      rewrite <- Eqdep_dec.eq_rect_eq_dec; [reflexivity | ].
      apply eq_dec.
    - eauto.
  Qed.

  Ltac t_interp_circuit_willFire_of_canFire :=
        repeat match goal with
           | _ => progress intros
           | _ => reflexivity
           | _ => progress cbn
           | [ H: _ = _ |- _ ] => rewrite H
           | _ => destruct (Bits.single _)
           end.

  Ltac t_interp_circuit_willFire_of_canFire_impl :=
    repeat match goal with
           | _ => reflexivity
           | _ => cleanup_step
           | _ => progress (unfold willFire_of_canFire'; cbn; intros)
           | [ H: Ob~_ = Ob~_ |- _ ] => apply (f_equal Bits.single) in H; cbn in H
           | [  |- Ob~_ = Ob~_ ] => f_equal
           | [ H: _ && _ = true |- _ ] => rewrite andb_true_iff in H
           | [ H: _ = _ |- _ ] => rewrite H
           | _ => rewrite !orb_true_r
           end.

  Lemma interp_circuit_willFire_of_canFire_read0:
    forall {tau} (rwd : rwdata R Sigma tau) cLog
      cOne (cdata0 cdata1 : circuit tau),
      interp_circuit' cOne = Ob~1 ->
      interp_circuit'
        (willFire_of_canFire'
           {| read0 := cOne;
              read1 := read1 rwd;
              write0 := write0 rwd;
              write1 := write1 rwd;
              data0 := cdata0;
              data1 := cdata1 |} cLog) =
      Ob~(Bits.single (interp_circuit' (willFire_of_canFire' rwd cLog)) &&
          negb (Bits.single (interp_circuit' cLog.(write0))) &&
          negb (Bits.single (interp_circuit' cLog.(write1)))).
  Proof.
    t_interp_circuit_willFire_of_canFire.
  Qed.

  Lemma interp_circuit_willFire_of_canFire_read1:
    forall {tau} (rwd : rwdata R Sigma tau) cLog
      cOne (cdata0 cdata1 : circuit tau),
      interp_circuit' cOne = Ob~1 ->
      interp_circuit'
        (willFire_of_canFire'
           {| read0 := read0 rwd;
              read1 := cOne;
              write0 := write0 rwd;
              write1 := write1 rwd;
              data0 := cdata0;
              data1 := cdata1 |} cLog) =
      Ob~(Bits.single (interp_circuit' (willFire_of_canFire' rwd cLog)) &&
          negb (Bits.single (interp_circuit' (write1 cLog)))).
  Proof.
    t_interp_circuit_willFire_of_canFire.
  Qed.

  Lemma interp_circuit_willFire_of_canFire_write0:
    forall {tau} (rwd : rwdata R Sigma tau) cLog
      cOne (cdata0 cdata1 : circuit tau),
      interp_circuit' cOne = Ob~1 ->
      interp_circuit'
        (willFire_of_canFire'
           {| read0 := read0 rwd;
              read1 := read1 rwd;
              write0 := cOne;
              write1 := write1 rwd;
              data0 := cdata0;
              data1 := cdata1 |} cLog) =
      Ob~(Bits.single (interp_circuit' (willFire_of_canFire' rwd cLog)) &&
          negb (Bits.single (interp_circuit' cLog.(write0))) &&
          negb (Bits.single (interp_circuit' cLog.(write1))) &&
          negb (Bits.single (interp_circuit' cLog.(read1)))).
  Proof.
    t_interp_circuit_willFire_of_canFire.
  Qed.

  Lemma interp_circuit_willFire_of_canFire_write1:
    forall {tau} (rwd : rwdata R Sigma tau) cLog
      cOne (cdata0 cdata1 : circuit tau),
      interp_circuit' cOne = Ob~1 ->
      interp_circuit'
        (willFire_of_canFire'
           {| read0 := read0 rwd;
              read1 := read1 rwd;
              write0 := write0 rwd;
              write1 := cOne;
              data0 := cdata0;
              data1 := cdata1 |} cLog) =
      Ob~(Bits.single (interp_circuit' (willFire_of_canFire' rwd cLog)) &&
          negb (Bits.single (interp_circuit' (write1 cLog)))).
  Proof.
    t_interp_circuit_willFire_of_canFire.
  Qed.

  Lemma interp_circuit_willFire_of_canFire_read0_impl:
    forall {tau} (rwd : rwdata R Sigma tau) cLog
      cOne (cdata0 cdata1 : circuit tau),
      interp_circuit' cLog.(write0) = Ob~0 ->
      interp_circuit' cLog.(write1) = Ob~0 ->
      interp_circuit' cOne = Ob~1 ->
      interp_circuit' (willFire_of_canFire' rwd cLog) = Ob~1 ->
      interp_circuit'
        (willFire_of_canFire'
           {| read0 := cOne;
              read1 := read1 rwd;
              write0 := write0 rwd;
              write1 := write1 rwd;
              data0 := cdata0;
              data1 := cdata1 |} cLog) = Ob~1.
  Proof.
    t_interp_circuit_willFire_of_canFire_impl.
  Qed.

  Lemma interp_circuit_willFire_of_canFire_read1_impl:
    forall {tau} (rwd : rwdata R Sigma tau) cLog
      cOne (cdata0 cdata1 : circuit tau),
      interp_circuit' (write1 cLog) = Ob~0 ->
      interp_circuit' cOne = Ob~1 ->
      interp_circuit' (willFire_of_canFire' rwd cLog) = Ob~1 ->
      interp_circuit'
        (willFire_of_canFire'
           {| read0 := read0 rwd;
              read1 := cOne;
              write0 := write0 rwd;
              write1 := write1 rwd;
              data0 := cdata0;
              data1 := cdata1 |} cLog) = Ob~1.
  Proof.
    t_interp_circuit_willFire_of_canFire_impl.
  Qed.

  Lemma interp_circuit_willFire_of_canFire_write0_impl:
    forall {tau} (rwd : rwdata R Sigma tau) cLog
      cOne (cdata0 cdata1 : circuit tau),
      interp_circuit' cLog.(write0) = Ob~0 ->
      interp_circuit' cLog.(write1) = Ob~0 ->
      interp_circuit' cLog.(read1) = Ob~0 ->
      interp_circuit' cOne = Ob~1 ->
      interp_circuit' (willFire_of_canFire' rwd cLog) = Ob~1 ->
      interp_circuit'
        (willFire_of_canFire'
           {| read0 := read0 rwd;
              read1 := read1 rwd;
              write0 := cOne;
              write1 := write1 rwd;
              data0 := cdata0;
              data1 := cdata1 |} cLog) = Ob~1.
  Proof.
    t_interp_circuit_willFire_of_canFire_impl.
  Qed.

  Lemma interp_circuit_willFire_of_canFire_write1_impl:
    forall {tau} (rwd : rwdata R Sigma tau) cLog
      cOne (cdata0 cdata1 : circuit tau),
      interp_circuit' (write1 cLog) = Ob~0 ->
      interp_circuit' cOne = Ob~1 ->
      interp_circuit' (willFire_of_canFire' rwd cLog) = Ob~1 ->
      interp_circuit'
        (willFire_of_canFire'
           {| read0 := read0 rwd;
              read1 := read1 rwd;
              write0 := write0 rwd;
              write1 := cOne;
              data0 := cdata0;
              data1 := cdata1 |} cLog) = Ob~1.
  Proof.
    t_interp_circuit_willFire_of_canFire_impl.
  Qed.

  Hint Extern 1 => eapply circuit_gamma_equiv_CtxCons : circuits.

  Hint Resolve
       circuit_lt_CAnnot_l
       circuit_lt_CAnnot_r
       circuit_lt_CAnd
       circuit_lt_CAnd_l
       circuit_lt_CAnd_r
       circuit_lt_COr
       circuit_lt_CNot
       circuit_lt_true
       circuit_lt_false
       circuit_lt_refl
       circuit_lt_true
       circuit_lt_false
       rwset_circuit_lt_invariant_putenv
       rwset_circuit_lt_invariant_refl : circuits.
  Hint Extern 3 => cbn in * : circuits.
  Hint Extern 3 => red : circuits.

  Ltac t_step :=
    match goal with
    | _ => cleanup_step
    | _ => progress intros
    | _ => progress cbn in *
    | [ H: _ \/ _ |- _ ] => destruct H
    | [ H: exists _, _ |- _ ] => destruct H
    | [  |- Ob~_ = Ob~_ ] => f_equal
    | [ H: ?x = true |- context[?x] ] => rewrite H
    | [ H: ?x = false |- context[?x] ] => rewrite H
    | [ H: interp_circuit' ?c = Ob~_ |- context[interp_circuit' ?c] ] =>
      rewrite H
    | [ Heq: interp_circuit ?x = Some _ |- context[interp_circuit ?x] ] =>
      rewrite Heq
    | [ IH: context[interp_expr _ _ _ _ _ ?ex] |-
        context[interp_expr _ _ ?Gamma ?Log ?log ?ex] ] =>
      specialize (IH _ Gamma _ log ltac:(ceauto) ltac:(ceauto) ltac:(ceauto) ltac:(ceauto));
      cbv zeta in IH;
      destruct (interp_expr _ _ Gamma Log log ex) as [(? & ?) | ] eqn:?; cbn
    | [ |- match (if ?x then _ else _) with _ => _ end ] =>
      destruct x eqn:?; cbn
    | [ IH: context[interp_rule _ _ _ _ _ ?rl] |-
        context[interp_rule _ _ ?Gamma ?Log ?log ?rl] ] =>
      specialize (IH _ Gamma _ log ltac:(ceauto) ltac:(ceauto) ltac:(ceauto) ltac:(ceauto));
      cbv zeta in IH;
      destruct (interp_rule _ _ Gamma Log log rl) as [? | ] eqn:?; cbn
    | [  |- context[REnv.(getenv) (REnv.(map2) _ _ _)] ] =>
      unfold map2; rewrite !getenv_create
    end.

  (* Create HintDb circuits discriminated. *)
  Ltac t := repeat t_step; eauto.  (* with circuits. *)

  Ltac interp_willFire_cleanup :=
    repeat match goal with
           | _ => reflexivity
           | [ H: interp_circuit' (willFire_of_canFire _ _) = Ob~1 |- _ ] =>
             rewrite interp_willFire_of_canFire_true in H
           | [ H: interp_circuit' (willFire_of_canFire _ _) = Ob~0 |- _ ] =>
             rewrite interp_willFire_of_canFire_false in H
           | [ |- interp_circuit' (willFire_of_canFire _ _) = Ob~1 ] =>
             rewrite interp_willFire_of_canFire_true
           | [ |- interp_circuit' (willFire_of_canFire _ _) = Ob~0 ] =>
             rewrite interp_willFire_of_canFire_false
           | _ => progress cbn
           | _ => progress intros
           | [  |- _ /\ _ ] => split
           | [ H: _ /\ _ |- _ ] => destruct H
           | [  |- Ob~_ = Ob~_ ] => f_equal
           | [  |- _ && _ = true ] => rewrite andb_true_intro; split
           | [  |- context[REnv.(getenv) (REnv.(putenv) _ ?idx _) ?idx'] ] =>
             destruct (eq_dec idx idx'); subst;
             [ rewrite !get_put_eq | rewrite !get_put_neq by eassumption ];
             [ | solve [intuition eauto] ]
           | [  |- interp_circuit' (willFire_of_canFire' _ _) = Ob~_ ] =>
             (rewrite interp_circuit_willFire_of_canFire_read0 ||
              rewrite interp_circuit_willFire_of_canFire_read1 ||
              rewrite interp_circuit_willFire_of_canFire_write0 ||
              rewrite interp_circuit_willFire_of_canFire_write1);
             [ .. | solve[intuition eauto] ]
           | [ H: context[interp_circuit' _ = _] |-
               context[interp_circuit' _] ] =>
             rewrite H
           end; cbn.

  Arguments willFire_of_canFire' : simpl never.

  Lemma expr_compiler_correct {sig tau} Log cLog:
    forall (ex: expr sig tau) (clog: rule_circuit)
      (Gamma: vcontext sig) (gamma: ccontext sig) log,
      log_rwdata_consistent log clog.(regs) ->
      circuit_gamma_equiv Gamma gamma ->
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
          -- interp_willFire_cleanup.
             admit. admit. admit.
        * interp_willFire_cleanup. t.
          (* may_read0 says there could be three cases: write0 or write1 in L, or write1 in l *)
          (* cut ((interp_circuit' (read1 (getenv REnv (regs clog) idx))) = Ob~1 \/ *)
          (*      (interp_circuit' (write1 (getenv REnv (regs clog) idx))) = Ob~1). *)
          admit.
      + cbn.
        destruct (may_read1 Log idx) eqn:?; cbn.
        * repeat split.
          -- admit. (* Log consistency -> retVal *)
          -- admit. (* Log consistency property *)
          -- interp_willFire_cleanup.
             admit.
        * interp_willFire_cleanup.
          right.
          eexists.
          interp_willFire_cleanup.
          admit.
    - (* Call *)
      repeat t_step; eauto.
      eapply interp_circuit_circuit_lt_helper_false;
        eauto using expr_compile_willFire_of_canFire_decreasing.
  Admitted.

  Lemma interp_circuit_willFire_of_canFire'_mux_rwdata:
    forall (idx : reg_t) (rwd1 rwd2 : rwdata R Sigma (R idx)) (cCond : circuit 1) (rwdL : rwdata R Sigma (R idx)),
      interp_circuit' (willFire_of_canFire' (mux_rwdata cCond rwd1 rwd2) rwdL) =
      if Bits.single (interp_circuit' cCond) then
        interp_circuit' (willFire_of_canFire' rwd1 rwdL)
      else
        interp_circuit' (willFire_of_canFire' rwd2 rwdL).
  Proof.
    intros *;
      unfold willFire_of_canFire'; cbn;
        destruct (interp_circuit' cCond) as [ [ | ] [ ] ];
        cbn; eauto.
  Qed.

  (* Lemma interp_circuit_willFire_of_canFire'_mux_rwdata: *)
  (*   forall (idx : reg_t) (rwd1 rwd2 : rwdata R Sigma (R idx)) (cCond : circuit 1) (rwdL : rwdata R Sigma (R idx)), *)
  (*     (interp_circuit' cCond = Ob~1 -> interp_circuit' (willFire_of_canFire' rwd1 rwdL) = Ob~1) -> *)
  (*     (interp_circuit' cCond = Ob~0 -> interp_circuit' (willFire_of_canFire' rwd2 rwdL) = Ob~1) -> *)
  (*     interp_circuit' (willFire_of_canFire' (mux_rwdata cCond rwd1 rwd2) rwdL) = Ob~1. *)
  (* Proof. *)
  (*   intros *; *)
  (*     unfold willFire_of_canFire'; cbn; *)
  (*       destruct (interp_circuit' cCond) as [ [ | ] [ ] ]; *)
  (*       cbn; eauto. *)
  (* Qed. *)

  (* Lemma interp_circuit_willFire_of_canFire'_mux_rwdata_left: *)
  (*   forall (idx : reg_t) (rwd1 rwd2 : rwdata R Sigma (R idx)) (cCond : circuit 1) (rwdL : rwdata R Sigma (R idx)), *)
  (*     interp_circuit' cCond = Ob~1 -> *)
  (*     interp_circuit' (willFire_of_canFire' rwd1 rwdL) = Ob~1 -> *)
  (*     interp_circuit' (willFire_of_canFire' (mux_rwdata cCond rwd1 rwd2) rwdL) = Ob~1. *)
  (* Proof. *)
  (*   intros; apply interp_circuit_willFire_of_canFire'_mux_rwdata; eauto. *)
  (*   intros H'; rewrite H' in *; discriminate. *)
  (* Qed. *)

  (* Lemma interp_circuit_willFire_of_canFire'_mux_rwdata_right: *)
  (*   forall (idx : reg_t) (rwd1 rwd2 : rwdata R Sigma (R idx)) (cCond : circuit 1) (rwdL : rwdata R Sigma (R idx)), *)
  (*     interp_circuit' cCond = Ob~0 -> *)
  (*     interp_circuit' (willFire_of_canFire' rwd2 rwdL) = Ob~1 -> *)
  (*     interp_circuit' (willFire_of_canFire' (mux_rwdata cCond rwd1 rwd2) rwdL) = Ob~1. *)
  (* Proof. *)
  (*   intros; apply interp_circuit_willFire_of_canFire'_mux_rwdata; eauto. *)
  (*   intros H'; rewrite H' in *; discriminate. *)
  (* Qed. *)

  Lemma rule_compiler_correct {sig} Log cLog:
    forall (rl: rule sig) (clog: rule_circuit)
      (Gamma: vcontext sig) (gamma: ccontext sig) log,
      log_rwdata_consistent log clog.(regs) ->
      circuit_gamma_equiv Gamma gamma ->
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
    induction rl; intros; try solve [cbn; eauto].
    - (* Fail *)
      t; interp_willFire_cleanup; t.
    - (* Seq *)
      t.
      eapply interp_circuit_circuit_lt_helper_false;
        eauto using rule_compile_willFire_of_canFire_decreasing.
    - (* Bind *)
      pose proof (@expr_compiler_correct sig tau Log cLog ex).
      t.
      eapply interp_circuit_circuit_lt_helper_false;
        eauto using rule_compile_willFire_of_canFire_decreasing.
    - (* If *)
      pose proof (@expr_compiler_correct sig _ Log cLog cond).
      t.
      + split.
        admit.                  (* log consistency *)
        interp_willFire_cleanup; split; t.
        rewrite interp_circuit_willFire_of_canFire'_mux_rwdata; t.
      + interp_willFire_cleanup; t.
        right. exists x; t.
        rewrite interp_circuit_willFire_of_canFire'_mux_rwdata; t.
      + split.
        admit.                  (* log consistency *)
        interp_willFire_cleanup; split; t.
        rewrite interp_circuit_willFire_of_canFire'_mux_rwdata; t.
      + interp_willFire_cleanup; t.
        right; exists x; t.
        rewrite interp_circuit_willFire_of_canFire'_mux_rwdata; t.
      + interp_willFire_cleanup; t.
        * left.
          lazymatch goal with
          | [  |- (if ?c then _ else _) = _ ] => destruct c
          end;
            (eapply interp_circuit_circuit_lt_helper_false;
             [ apply rwset_circuit_lt_compile_rule_correct | ]; eauto).
        * right.
          exists x; t.
          rewrite interp_circuit_willFire_of_canFire'_mux_rwdata; t.
          destruct Bits.single; t;
            eapply interp_circuit_circuit_lt_helper_false;
            eauto using rule_compile_willFire_of_canFire'_decreasing.
    - (* Write *)
      pose proof (@expr_compiler_correct sig _ Log cLog value).
      t.
      + split.
        * admit. (* consistent. *)
        * destruct port.
          -- interp_willFire_cleanup; t; split.
             ++ admit.
             ++
               repeat match goal with
                      end.

                admit.
                admit.
                admit.
          -- interp_willFire_cleanup; t; split.
             ++ admit.
             ++ intros; destruct (eq_dec idx idx0); subst;
                  [ rewrite !get_put_eq | rewrite !get_put_neq by eassumption ];
                  eauto.

                  lazymatch goal with
                  | [ H: Ob~_ = Ob~_ |- _ ] => apply (f_equal Bits.single) in H; cbn in H
                  end.

                  unfold willFire_of_canFire'; cbn; intros * H **.
                  ; f_equal.


                  intros cLog idx0 rwd cdata1.

                specialize (H5 idx0).
                unfold willFire_of_canFire' in H5 |- *. cbn in *.
                rewrite orb_true_r.
                apply (f_equal Bits.single) in H5; cbn in H5.
                f_equal.
                rewrite !andb_true_iff in *; cbn.
                clear -H5.
                intuition eauto.
                intuition eauto.
                rewrite H5.
                apply bits_single_bits_cons in H5.
                cbn.
                bool_simpl.
                admit.

      + admit. (* may write false *)
      + destruct port;
          eapply interp_circuit_circuit_lt_helper_false; eauto;
            intros; apply circuit_lt_willFire_of_canFire; cbn;
              eauto 8 with circuits.
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
