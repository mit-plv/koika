Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Ring Coq.setoid_ring.Ring.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import
        Koika.Common Koika.Environments Koika.Syntax
        Koika.SemanticProperties Koika.CircuitProperties Koika.PrimitiveProperties
        Koika.Interop.

Section PrimCompilerCorrectness.
  Context {pos_t var_t rule_name_t reg_t ext_fn_t: Type}.

  Context {R: reg_t -> type}.
  Context {Sigma: ext_fn_t -> ExternalSignature}.

  Context {REnv: Env reg_t}.
  Context (cr: REnv.(env_t) (fun idx => bits (CR_of_R R idx))).
  Context (csigma: forall f, CSigma_of_Sigma Sigma f).

  Notation interp_circuit := (interp_circuit (rule_name_t := rule_name_t) cr csigma).

  Ltac compile_op_t :=
    match goal with
    | _ => progress intros
    | _ => progress simpl in *
    | _ => progress unfold Bits.extend_beginning, Bits.extend_end, struct_sz, field_sz
    | _ => rewrite bits_of_value_of_bits
    | [ H: interp_circuit _ = _ |- _ ] => rewrite H
    | [  |- context[match ?d with _ => _ end] ] => is_var d; destruct d
    | [  |- context[eq_rect _ _ _ _ ?pr] ] => destruct pr
    | _ => apply bits_eq_of_value || apply get_field_bits_part || apply subst_field_bits_part_subst
    | _ => solve [eauto]
    end.

  Theorem compile_unop_correct :
    forall fn c a,
      interp_circuit c = bits_of_value a ->
      interp_circuit (compile_unop fn c) = bits_of_value (PrimSpecs.sigma1 fn a).
  Proof.
    destruct fn; repeat compile_op_t.
  Qed.

  Theorem compile_binop_correct :
    forall fn c1 c2 a1 a2,
      interp_circuit c1 = bits_of_value a1 ->
      interp_circuit c2 = bits_of_value a2 ->
      interp_circuit (compile_binop fn c1 c2) = bits_of_value (PrimSpecs.sigma2 fn a1 a2).
  Proof.
    destruct fn; repeat compile_op_t.
  Qed.
End PrimCompilerCorrectness.

Section CompilerCorrectness.
  Context {pos_t var_t rule_name_t reg_t ext_fn_t: Type}.

  Context {R: reg_t -> type}.
  Notation CR := (CR_of_R R).

  Context {Sigma: ext_fn_t -> ExternalSignature}.
  Notation CSigma := (CSigma_of_Sigma Sigma).

  Context {REnv: Env reg_t}.

  Context (r: REnv.(env_t) R).
  Notation cr := (cr_of_r r).

  Instance reg_t_eq_dec : EqDec reg_t := @EqDec_FiniteType _ (REnv.(finite_keys)).

  Notation rwdata := (rwdata (rule_name_t := rule_name_t) R Sigma).

  Context (sigma: forall f, Sigma f).
  Context (csigma: forall f, CSigma f).
  Context {csigma_correct: csigma_spec sigma csigma}.
  Context (lco: (@local_circuit_optimizer
                   rule_name_t reg_t ext_fn_t CR CSigma
                   rwdata csigma)).

  Open Scope bool_scope.

  Notation Log := (Log R REnv).
  Notation rwset := (rwset (rule_name_t := rule_name_t)).
  Notation circuit := (circuit (rule_name_t := rule_name_t) (rwdata := rwdata) CR CSigma).
  Notation scheduler_circuit := (scheduler_circuit (rule_name_t := rule_name_t) R Sigma REnv).
  Notation action := (action pos_t var_t R Sigma).
  Notation rule := (rule pos_t var_t R Sigma).
  Notation interp_circuit := (interp_circuit (rule_name_t := rule_name_t) cr csigma).
  Notation circuit_lt := (circuit_lt r csigma).

  Context (rc: REnv.(env_t) (fun reg => circuit (CR reg))).

  Definition circuit_env_equiv :=
    forall idx, interp_circuit (REnv.(getenv) rc idx) = bits_of_value (REnv.(getenv) r idx).

  Definition log_data0_consistent' (l: Log) (regs: rwset) :=
    forall idx,
      let cidx := REnv.(getenv) regs idx in
      interp_circuit (cidx.(data0)) =
      bits_of_value
      match latest_write0 l idx with
      | Some v => v
      | None => getenv REnv r idx
      end.

  Definition log_data0_consistent (l L: Log) (regs: rwset) :=
    log_data0_consistent' (log_app l L) regs.

  Definition log_data1_consistent' (l: Log) (regs: rwset) :=
    forall idx,
      let cidx := REnv.(getenv) regs idx in
      log_existsb l idx is_write1 = true ->
      match latest_write1 l idx with
      | Some v => interp_circuit (cidx.(data1)) = bits_of_value v
      | None => False
      end.

  Definition log_data1_consistent (l L: Log) (regs: rwset) :=
    log_data1_consistent' (log_app l L) regs.

  Ltac data_consistent_putenv_t :=
    unfold log_data0_consistent, log_data0_consistent', log_data1_consistent, log_data1_consistent';
    repeat match goal with
           | _ => progress intros
           | [ H: _ = _ |- _ ] => rewrite H
           | [ H: forall idx, _, idx: reg_t |- _ ] => pose_once H idx
           | [  |- context[REnv.(getenv) (REnv.(putenv) _ ?idx _) ?idx'] ] =>
             destruct (eq_dec idx idx'); subst;
             [ rewrite !get_put_eq | rewrite !get_put_neq by eassumption ]
           | _ => progress rewrite ?latest_write0_app, ?latest_write1_app in *
           | _ => progress rewrite ?latest_write0_cons_eq, ?latest_write0_cons_neq
           | _ => progress rewrite ?latest_write1_cons_eq, ?latest_write1_cons_neq
           end; eauto.

  Lemma log_data0_consistent_putenv_read_write1 :
    forall idx k p log Log rws rwd v,
      k = LogRead \/ (k = LogWrite /\ p = P1) ->
      data0 rwd = data0 (REnv.(getenv) rws idx) ->
      log_data0_consistent log Log rws ->
      log_data0_consistent (log_cons idx {| kind := k; port := p; val := v |} log) Log
                            (REnv.(putenv) rws idx rwd).
  Proof.
    destruct 1; repeat cleanup_step; subst.
    all: data_consistent_putenv_t.
  Qed.

  Lemma log_data0_consistent_putenv_write0 :
    forall idx log Log rws rwd v,
      bits_of_value v = interp_circuit (data0 rwd) ->
      log_data0_consistent log Log rws ->
      log_data0_consistent (log_cons idx {| kind := LogWrite; port := P0; val := v |} log) Log
                            (REnv.(putenv) rws idx rwd).
  Proof.
    data_consistent_putenv_t.
  Qed.

  Ltac bool_cleanup :=
    match goal with
    | _ => reflexivity
    | _ => cleanup_step
    | [ H: _ \/ _ |- _ ] => destruct H
    | _ => bool_step
    | [ H: log_existsb (log_app _ _) _ _ = _ |- _ ] =>
      rewrite log_existsb_app in H
    | [ H: ?x = _ |- context[?x] ] =>
      rewrite H
    | _ => progress bool_simpl
    end.

  Lemma log_existsb_app_cons_write1_eq:
    forall idx k p (log: Log) Log v,
      k = LogRead \/ (k = LogWrite /\ p = P0) ->
      log_existsb (log_app (log_cons idx {| kind := k; port := p; val := v |} log) Log) idx is_write1 = true ->
      log_existsb (log_app log Log) idx is_write1 = true.
  Proof.
    destruct 1; repeat cleanup_step; subst.

    all: rewrite !log_existsb_app; intros H; bool_cleanup; destruct H;
      try rewrite log_existsb_log_cons_eq in H; eauto; bool_simpl; try rewrite H; bool_simpl; reflexivity.
  Qed.

  Lemma log_existsb_app_cons_write1_neq:
    forall idx idx' k p (log: Log) Log v,
      idx <> idx' ->
      log_existsb (log_app (log_cons idx' {| kind := k; port := p; val := v |} log) Log) idx is_write1 = true ->
      log_existsb (log_app log Log) idx is_write1 = true.
  Proof.
    intros *.
    rewrite !log_existsb_app; intros Hneq H; bool_cleanup; destruct H;
      try rewrite log_existsb_log_cons_neq in H; eauto; bool_simpl; try rewrite H; bool_simpl; reflexivity.
  Qed.

  Lemma log_data1_consistent_putenv_read_write0 :
    forall idx k p log Log rws rwd v,
      k = LogRead \/ (k = LogWrite /\ p = P0) ->
      data1 rwd = data1 (REnv.(getenv) rws idx) ->
      log_data1_consistent log Log rws ->
      log_data1_consistent (log_cons idx {| kind := k; port := p; val := v |} log) Log
                            (REnv.(putenv) rws idx rwd).
  Proof.
    destruct 1; repeat cleanup_step; subst.

    all: data_consistent_putenv_t.

    all: match goal with
         | [ Hnew: _ <> _, H: log_existsb _ _ _ = _ -> _ |- _ ] =>
           apply H;
             eapply log_existsb_app_cons_write1_neq;
             try eassumption; eauto
         | [ H: log_existsb _ _ _ = _ -> _ |- _ ] =>
           apply H;
             eapply log_existsb_app_cons_write1_eq;
             try eassumption; eauto
         end.
  Qed.

  Lemma log_data1_consistent_putenv_write1 :
    forall idx log Log rws rwd v,
      bits_of_value v = interp_circuit (data1 rwd) ->
      log_data1_consistent log Log rws ->
      log_data1_consistent (log_cons idx {| kind := LogWrite; port := P1; val := v |} log) Log
                            (REnv.(putenv) rws idx rwd).
  Proof.
    data_consistent_putenv_t.
    apply H2.
    eapply log_existsb_app_cons_write1_neq; eauto.
  Qed.

  Ltac log_consistent_mux_t :=
    intros cond * H0 H1 idx;
    unfold mux_rwsets; rewrite !getenv_map2;
    unfold mux_rwdata; cbn;
    rewrite !lco_proof; cbn;
    destruct (interp_circuit cond) as [ [ | ] [] ]; cbn;
    [ specialize (H1 eq_refl idx) | specialize (H0 eq_refl idx) ];
    eauto.

  Arguments EqDec_ListBool : simpl never.

  Lemma log_data0_consistent'_mux :
    forall cond rws0 rws1 s l,
      (interp_circuit cond = Ob~0 -> log_data0_consistent' l rws0) ->
      (interp_circuit cond = Ob~1 -> log_data0_consistent' l rws1) ->
      log_data0_consistent' l (mux_rwsets lco s cond rws1 rws0).
  Proof.
    log_consistent_mux_t.
  Qed.

  Tactic Notation "log_consistent_mux_t'" constr(thm) :=
    intros; apply thm;
    eauto;
    let Heq := fresh in
    intros Heq; rewrite Heq in *; discriminate.

  Notation mux_rwsets := (mux_rwsets lco).

  Lemma log_data0_consistent'_mux_l :
    forall cond rws0 rws1 s l,
      interp_circuit cond = Ob~1 ->
      log_data0_consistent' l rws1 ->
      log_data0_consistent' l (mux_rwsets s cond rws1 rws0).
  Proof.
    log_consistent_mux_t' log_data0_consistent'_mux.
  Qed.

  Lemma log_data0_consistent'_mux_r :
    forall cond rws0 rws1 s l,
      interp_circuit cond = Ob~0 ->
      log_data0_consistent' l rws0 ->
      log_data0_consistent' l (mux_rwsets s cond rws1 rws0).
  Proof.
    log_consistent_mux_t' log_data0_consistent'_mux.
  Qed.

  Lemma log_data0_consistent_mux_l :
    forall cond rws0 rws1 s l L,
      interp_circuit cond = Ob~1 ->
      log_data0_consistent l L rws1 ->
      log_data0_consistent l L (mux_rwsets s cond rws1 rws0).
  Proof.
    log_consistent_mux_t' log_data0_consistent'_mux.
  Qed.

  Lemma log_data0_consistent_mux_r :
    forall cond rws0 rws1 s l L,
      interp_circuit cond = Ob~0 ->
      log_data0_consistent l L rws0 ->
      log_data0_consistent l L (mux_rwsets s cond rws1 rws0).
  Proof.
    log_consistent_mux_t' log_data0_consistent'_mux.
  Qed.

  Lemma log_data1_consistent'_mux :
    forall cond rws0 rws1 s l,
      (interp_circuit cond = Ob~0 -> log_data1_consistent' l rws0) ->
      (interp_circuit cond = Ob~1 -> log_data1_consistent' l rws1) ->
      log_data1_consistent' l (mux_rwsets s cond rws1 rws0).
  Proof.
    log_consistent_mux_t.
  Qed.

  Lemma log_data1_consistent'_mux_l :
    forall cond rws0 rws1 s l,
      interp_circuit cond = Ob~1 ->
      log_data1_consistent' l rws1 ->
      log_data1_consistent' l (mux_rwsets s cond rws1 rws0).
  Proof.
    log_consistent_mux_t' log_data1_consistent'_mux.
  Qed.

  Lemma log_data1_consistent'_mux_r :
    forall cond rws0 rws1 s l,
      interp_circuit cond = Ob~0 ->
      log_data1_consistent' l rws0 ->
      log_data1_consistent' l (mux_rwsets s cond rws1 rws0).
  Proof.
    log_consistent_mux_t' log_data1_consistent'_mux.
  Qed.

  Definition log_rwdata_consistent (log: Log) (regs: rwset) :=
    forall idx,
      let cidx := REnv.(getenv) regs idx in
      (interp_circuit (cidx.(read0)) = Ob~(log_existsb log idx is_read0)) /\
      (interp_circuit (cidx.(read1)) = Ob~(log_existsb log idx is_read1)) /\
      (interp_circuit (cidx.(write0)) = Ob~(log_existsb log idx is_write0)) /\
      (interp_circuit (cidx.(write1)) = Ob~(log_existsb log idx is_write1)).

  Definition log_rwdata_consistent_update {sz} kind port (rwd rwd': rwdata sz) :=
    interp_circuit (read0 rwd) =
    Ob~(is_read0 kind port || Bits.single (interp_circuit (read0 rwd'))) /\
    interp_circuit (read1 rwd) =
    Ob~(is_read1 kind port || Bits.single (interp_circuit (read1 rwd'))) /\
    interp_circuit (write0 rwd) =
    Ob~(is_write0 kind port || Bits.single (interp_circuit (write0 rwd'))) /\
    interp_circuit (write1 rwd) =
    Ob~(is_write1 kind port || Bits.single (interp_circuit (write1 rwd'))).

  Lemma log_rwdata_consistent_log_cons_putenv :
    forall (log: Log) idx (regs: rwset) rwd le,
      log_rwdata_consistent log regs ->
      log_rwdata_consistent_update le.(kind) le.(port) rwd (REnv.(getenv) regs idx) ->
      log_rwdata_consistent (log_cons idx le log) (REnv.(putenv) regs idx rwd).
  Proof.
    unfold log_rwdata_consistent; intros *; destruct le;
      intros Heq Hcst **; destruct (eq_dec idx idx0); subst;
      [ rewrite !get_put_eq | rewrite !get_put_neq by eassumption ].
    - specialize (Heq idx0).
      rewrite !log_existsb_log_cons_eq.
      repeat cleanup_step.
      repeat match goal with
             | [ H: _ = _ |- _ ] => apply (f_equal Bits.single) in H; cbn in H
             | [ H: _ = _ |- _ ] => rewrite <- H
             end.
      apply Hcst.
    - rewrite !log_existsb_log_cons_neq;
        eauto.
  Qed.

  Lemma log_rwdata_consistent_mux :
    forall cond rws0 rws1 s l,
      (interp_circuit cond = Ob~0 -> log_rwdata_consistent l rws0) ->
      (interp_circuit cond = Ob~1 -> log_rwdata_consistent l rws1) ->
      log_rwdata_consistent l (mux_rwsets s cond rws1 rws0).
  Proof.
    log_consistent_mux_t.
  Qed.

  Lemma log_rwdata_consistent_mux_l :
    forall cond rws0 rws1 s l,
      interp_circuit cond = Ob~1 ->
      log_rwdata_consistent l rws1 ->
      log_rwdata_consistent l (mux_rwsets s cond rws1 rws0).
  Proof.
    log_consistent_mux_t' log_rwdata_consistent_mux.
  Qed.

  Lemma log_rwdata_consistent_mux_r :
    forall cond rws0 rws1 s l,
      interp_circuit cond = Ob~0 ->
      log_rwdata_consistent l rws0 ->
      log_rwdata_consistent l (mux_rwsets s cond rws1 rws0).
  Proof.
    log_consistent_mux_t' log_rwdata_consistent_mux.
  Qed.

  Ltac ceauto :=
    eauto with circuits.

  Notation willFire_of_canFire' := (willFire_of_canFire' lco).
  Notation willFire_of_canFire := (willFire_of_canFire lco).

  Lemma interp_willFire_of_canFire_canFire_false :
    forall (c: circuit 1) (rwd: rwset) (cLog: scheduler_circuit),
      interp_circuit c = Ob~0 ->
      interp_circuit (willFire_of_canFire {| canFire := c; regs := rwd |} cLog) = Ob~0.
  Proof.
    intros.
    eapply interp_circuit_circuit_lt_helper_false.
    apply circuit_lt_willFire_of_canFire_canFire.
    eassumption.
  Qed.

  Lemma interp_willFire_of_canFire_eqn :
    forall clog (cLog: scheduler_circuit),
      interp_circuit (willFire_of_canFire clog cLog) =
      Ob~(andb (Bits.single (interp_circuit (canFire clog)))
               (List.forallb (fun idx =>
                                (Bits.single
                                   (interp_circuit
                                      (willFire_of_canFire'
                                         (REnv.(getenv) clog.(regs) idx)
                                         (REnv.(getenv) cLog idx)))))
                             (finite_elements (FiniteType := finite_keys REnv)))).
  Proof.
    unfold willFire_of_canFire, Environments.fold_right; cbn.
    induction finite_elements; cbn; intros.
    - bool_simpl; rewrite Bits.single_cons; reflexivity.
    - rewrite getenv_zip; cbn.
      rewrite lco_proof; cbn.
      rewrite IHl; cbn.
      f_equal.
      rewrite <- !andb_assoc.
      f_equal.
      apply andb_comm.
  Qed.

  Opaque Circuits.willFire_of_canFire'.

  Lemma finite_In {T} {FT: FiniteType T}:
    forall t: T, List.In t finite_elements.
  Proof.
    eauto using nth_error_In, finite_surjective.
  Qed.

  Lemma interp_willFire_of_canFire_true :
    forall clog (cLog: scheduler_circuit),
      interp_circuit (willFire_of_canFire clog cLog) = Ob~1 <->
      interp_circuit (canFire clog) = Ob~1 /\
      forall idx, interp_circuit
               (willFire_of_canFire'
                  (REnv.(getenv) clog.(regs) idx)
                  (REnv.(getenv) cLog idx)) = Ob~1.
  Proof.
    split; intros * H.
    - rewrite interp_willFire_of_canFire_eqn in H.
      apply Bits.cons_inj in H; repeat cleanup_step || bool_step.
      split.
      + eauto using Bits.single_inj.
      + intros idx.
        lazymatch goal with
        | [ H: forallb _ _ = _ |- _ ] =>
          rewrite forallb_forall in H;
            specialize (H idx ltac:(eauto using @finite_In))
        end.
        eauto using Bits.single_inj.
    - repeat cleanup_step.
      rewrite interp_willFire_of_canFire_eqn.
      f_equal.
      apply (f_equal Bits.single) in H; cbn in H; rewrite H.
      bool_simpl.
      apply forallb_forall; intros idx **.
      rewrite H0; reflexivity.
  Qed.

  Lemma interp_willFire_of_canFire_false :
    forall clog (cLog: scheduler_circuit),
      interp_circuit (willFire_of_canFire clog cLog) = Ob~0 <->
      interp_circuit (canFire clog) = Ob~0 \/
      exists idx, interp_circuit
               (willFire_of_canFire'
                  (REnv.(getenv) clog.(regs) idx)
                  (REnv.(getenv) cLog idx)) = Ob~0.
  Proof.
    split; intros * H.
    - rewrite interp_willFire_of_canFire_eqn in H.
      apply Bits.cons_inj in H; repeat cleanup_step || bool_step; destruct H.
      + eauto using Bits.single_inj.
      + right. rewrite forallb_exists in H.
        destruct H as (idx & _ & Heq).
        eauto using Bits.single_inj.
    - rewrite interp_willFire_of_canFire_eqn; f_equal.
      rewrite andb_false_iff; destruct H as [ -> | ( idx & Heq ) ]; [left | right].
      + reflexivity.
      + rewrite forallb_exists.
        exists idx; rewrite Heq.
        eauto using @finite_In.
  Qed.

  Transparent Circuits.willFire_of_canFire'.

  Definition rwdata_circuit_lt_invariant {idx} (rwd1 rwd2: rwdata (R idx)) :=
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

  Notation mux_rwdata := (mux_rwdata lco).

  Lemma rwdata_circuit_lt_invariant_mux_rwdata_l :
    forall s c idx rwd1 rwd2 rwd3,
      (interp_circuit c = Ob~1 -> @rwdata_circuit_lt_invariant idx rwd1 rwd3) ->
      (interp_circuit c = Ob~0 -> @rwdata_circuit_lt_invariant idx rwd2 rwd3) ->
      @rwdata_circuit_lt_invariant idx (mux_rwdata s c rwd1 rwd2) rwd3.
  Proof.
    unfold rwdata_circuit_lt_invariant, mux_rwdata; cbn; intros.
    repeat split; apply circuit_lt_CAnnot_l, circuit_lt_opt_l, circuit_lt_CMux_l; intuition eauto.
  Qed.

  Lemma rwdata_circuit_lt_invariant_mux_rwdata_r :
    forall s c idx rwd1 rwd2 rwd3,
      (interp_circuit c = Ob~1 -> @rwdata_circuit_lt_invariant idx rwd1 rwd2) ->
      (interp_circuit c = Ob~0 -> @rwdata_circuit_lt_invariant idx rwd1 rwd3) ->
      @rwdata_circuit_lt_invariant idx rwd1 (mux_rwdata s c rwd2 rwd3).
  Proof.
    unfold rwdata_circuit_lt_invariant, mux_rwdata; cbn; intros.
    repeat split; apply circuit_lt_CAnnot_r, circuit_lt_opt_r, circuit_lt_CMux_r; intuition eauto.
  Qed.

  Notation compile_action := (compile_action lco).

  Ltac circuit_compile_destruct_t :=
    repeat lazymatch goal with
           | [ IH: context[Circuits.compile_action ?lco ?rc _ ?a _],
                   H: context[Circuits.compile_action ?lco ?rc ?gamma ?a ?rwc] |- _ ] =>
             specialize (IH gamma rwc _ _ (surjective_pairing _));
             destruct (Circuits.compile_action lco rc gamma a rwc); cbn
           | [ H: (_, _) = (_, _) |- _ ] => inversion H; subst; clear H
           end.

  Theorem rwset_circuit_lt_compile_action_correct {sig tau} :
    forall (gamma: ccontext sig) (a: action sig tau) (rwc: rwcircuit) c gamma',
      compile_action rc gamma a rwc = (c, gamma') ->
      circuit_lt (canFire (erwc c)) (canFire rwc) /\
      forall idx, rwset_circuit_lt_invariant (rwc.(regs)) (c.(erwc).(regs)) idx.
  Proof.
    induction a; cbn; intros; circuit_compile_destruct_t; cbn in *;
      try solve [split; circuit_lt_f_equal; eauto using rwset_circuit_lt_invariant_refl].

    - (* Assign *)
      intuition eauto using circuit_lt_trans, rwset_circuit_lt_invariant_trans.
    - (* Seq *)
      intuition eauto using circuit_lt_trans, rwset_circuit_lt_invariant_trans.
    - (* Bind *)
      intuition eauto using circuit_lt_trans, rwset_circuit_lt_invariant_trans.
    - (* If *)
      split.
      + circuit_lt_f_equal.
        apply circuit_lt_CMux_l;
          intuition eauto using circuit_lt_trans, rwset_circuit_lt_invariant_trans.
      + unfold mux_rwsets; red; intros.
        rewrite getenv_map2.
        apply rwdata_circuit_lt_invariant_mux_rwdata_r;
          intros; eapply rwset_circuit_lt_invariant_trans; intuition eauto.
    - destruct port; cbn; circuit_compile_destruct_t.
      (* Read0 *)
      + split.
        * apply circuit_lt_CAnnot_l, circuit_lt_opt_l, circuit_lt_CAnd_l, circuit_lt_refl.
        * intros. eapply rwset_circuit_lt_invariant_putenv.
          -- eauto using rwset_circuit_lt_invariant_refl.
          -- red; cbn; eauto using circuit_lt_true, circuit_lt_refl, circuit_lt_opt_r.
      (* Read1 *)
      + split.
        * eauto using circuit_lt_refl.
        * intros; apply rwset_circuit_lt_invariant_putenv.
          -- eauto using rwset_circuit_lt_invariant_refl.
          -- red; cbn; eauto using circuit_lt_true, circuit_lt_refl, circuit_lt_opt_r.
    - (* Write *)
      destruct port; cbn;
      circuit_compile_destruct_t;
      destruct IHa as (Hpr & Hpr'); split.
      all: circuit_lt_f_equal; eauto using circuit_lt_CAnd_l.
      all: intros; apply rwset_circuit_lt_invariant_putenv; eauto.
      all: specialize (Hpr' idx); repeat (red || red in Hpr'); cbn;
        intuition eauto using circuit_lt_true, circuit_lt_opt_r.
    - (* Unop *)
      circuit_compile_destruct_t.
      intuition eauto using circuit_lt_trans, rwset_circuit_lt_invariant_trans.
    - (* Binop *)
      circuit_compile_destruct_t.
      intuition eauto using circuit_lt_trans, rwset_circuit_lt_invariant_trans.
    - (* ExternalCall *)
      circuit_compile_destruct_t.
      intuition eauto using circuit_lt_trans, rwset_circuit_lt_invariant_trans.
    - (* APos *) eauto.
  Qed.

  Lemma circuit_lt_willFire_of_canFire':
    forall idx (rwd0 rwd1 rwd2: rwdata (R idx)),
      rwdata_circuit_lt_invariant rwd1 rwd0 ->
      circuit_lt (willFire_of_canFire' rwd0 rwd2) (willFire_of_canFire' rwd1 rwd2).
  Proof.
    unfold rwdata_circuit_lt_invariant; intros; repeat cleanup_step; circuit_lt_f_equal;
      eauto.
  Qed.

  Lemma circuit_lt_willFire_of_canFire :
    forall (l1 l2: rwcircuit) L,
      circuit_lt (canFire l1) (canFire l2) ->
      (forall idx, rwset_circuit_lt_invariant l2.(regs) l1.(regs) idx) ->
      circuit_lt (willFire_of_canFire l1 L) (willFire_of_canFire l2 L).
  Proof.
    unfold willFire_of_canFire; intros * Hlt Hfr.
    apply circuit_lt_fold_right.
    - eassumption.
    - intros; rewrite !getenv_zip; cbn.
      apply circuit_lt_CAnnot, circuit_lt_opt_l, circuit_lt_opt_r, circuit_lt_CAnd.
      assumption.
      apply circuit_lt_willFire_of_canFire'.
      apply Hfr.
  Qed.

  Lemma action_compile_willFire_of_canFire'_decreasing {sig}:
    forall t (ex : action sig t) (gamma : ccontext sig) (rwc : rwcircuit) idx rwd c gamma',
      compile_action rc gamma ex rwc = (c, gamma') ->
      circuit_lt (willFire_of_canFire' (getenv REnv (regs (erwc c)) idx) rwd)
                 (willFire_of_canFire' (getenv REnv (regs rwc) idx) rwd).
  Proof.
    intros. eapply circuit_lt_willFire_of_canFire', rwset_circuit_lt_compile_action_correct. eauto.
  Qed.

  Theorem action_compile_willFire_of_canFire_decreasing {sig}:
    forall t (ex : action sig t) (cLog : scheduler_circuit)
      (gamma : ccontext sig) (rwc : rwcircuit) c gamma',
      compile_action rc gamma ex rwc = (c, gamma') ->
      circuit_lt (willFire_of_canFire (erwc c) cLog)
                 (willFire_of_canFire rwc cLog).
  Proof.
    intros;
      eapply circuit_lt_willFire_of_canFire;
      eapply rwset_circuit_lt_compile_action_correct; eauto.
  Qed.

  Lemma willFire_of_canFire_decreasing :
    forall c1 c2 (cLog: scheduler_circuit) rws,
      circuit_lt c1 c2 ->
      circuit_lt (willFire_of_canFire {| canFire := c1; regs := rws |} cLog)
                 (willFire_of_canFire {| canFire := c2; regs := rws |} cLog).
  Proof.
    unfold willFire_of_canFire; intros.
    eapply circuit_lt_fold_right.
    - eassumption.
    - intros; rewrite !getenv_zip.
      cbn.
      eauto using circuit_lt_CAnnot, circuit_lt_opt_l, circuit_lt_opt_r, circuit_lt_CAnd, circuit_lt_refl.
  Qed.

  Context {var_t_eq_dec: EqDec var_t}.

  Definition circuit_gamma_equiv {sig} (Gamma : vcontext sig) (gamma : ccontext sig) :=
    forall (k: var_t) tau (m : member (k, tau) sig),
      interp_circuit (cassoc m gamma) = bits_of_value (cassoc m Gamma).


  Lemma circuit_gamma_equiv_empty :
    circuit_gamma_equiv CtxEmpty CtxEmpty.
  Proof.
    red; intros; elim (mdestruct m).
  Qed.

  Lemma circuit_gamma_equiv_CtxCons {sig}:
    forall Gamma gamma,
      circuit_gamma_equiv (Gamma: vcontext sig) (gamma: ccontext sig) ->
      forall (tau : type) (var : var_t) (t: tau) (c : circuit tau),
        interp_circuit c = bits_of_value t ->
        circuit_gamma_equiv (CtxCons (var, tau) t Gamma) (CtxCons (var, tau) c gamma).
  Proof.
    unfold circuit_gamma_equiv; intros.
    destruct (mdestruct m) as [(Heq & ->) | (m' & ->)]; cbn.
    - inversion Heq; subst.
      rewrite <- Eqdep_dec.eq_rect_eq_dec; [cbn; assumption | apply eq_dec].
    - eauto.
  Qed.

  Ltac t_interp_circuit_willFire_of_canFire :=
    repeat match goal with
           | _ => progress intros
           | _ => reflexivity
           | [ H: context[lco_fn] |- _ ] => rewrite lco_proof in H
           | [  |- context[lco_fn] ] => rewrite lco_proof
           | _ => progress cbn
           | [ H: _ = _ |- _ ] => rewrite H
           | _ => destruct (Bits.single _)
           end.

  Lemma interp_circuit_willFire_of_canFire_read0:
    forall {tau} (rwd : rwdata tau) cLog
      cOne (cdata0 cdata1 : circuit tau),
      interp_circuit cOne = Ob~1 ->
      interp_circuit
        (willFire_of_canFire'
           {| read0 := cOne;
              read1 := read1 rwd;
              write0 := write0 rwd;
              write1 := write1 rwd;
              data0 := cdata0;
              data1 := cdata1 |} cLog) =
      Ob~(Bits.single (interp_circuit (willFire_of_canFire' rwd cLog)) &&
          negb (Bits.single (interp_circuit cLog.(write0))) &&
          negb (Bits.single (interp_circuit cLog.(write1)))).
  Proof.
    t_interp_circuit_willFire_of_canFire.
  Qed.

  Lemma interp_circuit_willFire_of_canFire_read1:
    forall {tau} (rwd : rwdata tau) cLog
      cOne (cdata0 cdata1 : circuit tau),
      interp_circuit cOne = Ob~1 ->
      interp_circuit
        (willFire_of_canFire'
           {| read0 := read0 rwd;
              read1 := cOne;
              write0 := write0 rwd;
              write1 := write1 rwd;
              data0 := cdata0;
              data1 := cdata1 |} cLog) =
      Ob~(Bits.single (interp_circuit (willFire_of_canFire' rwd cLog)) &&
          negb (Bits.single (interp_circuit (write1 cLog)))).
  Proof.
    t_interp_circuit_willFire_of_canFire.
  Qed.

  Lemma interp_circuit_willFire_of_canFire_write0:
    forall {tau} (rwd : rwdata tau) cLog
      cOne (cdata0 cdata1 : circuit tau),
      interp_circuit cOne = Ob~1 ->
      interp_circuit
        (willFire_of_canFire'
           {| read0 := read0 rwd;
              read1 := read1 rwd;
              write0 := cOne;
              write1 := write1 rwd;
              data0 := cdata0;
              data1 := cdata1 |} cLog) =
      Ob~(Bits.single (interp_circuit (willFire_of_canFire' rwd cLog)) &&
          negb (Bits.single (interp_circuit cLog.(write0))) &&
          negb (Bits.single (interp_circuit cLog.(write1))) &&
          negb (Bits.single (interp_circuit cLog.(read1)))).
  Proof.
    t_interp_circuit_willFire_of_canFire.
  Qed.

  Lemma interp_circuit_willFire_of_canFire_write1:
    forall {tau} (rwd : rwdata tau) cLog
      cOne (cdata0 cdata1 : circuit tau),
      interp_circuit cOne = Ob~1 ->
      interp_circuit
        (willFire_of_canFire'
           {| read0 := read0 rwd;
              read1 := read1 rwd;
              write0 := write0 rwd;
              write1 := cOne;
              data0 := cdata0;
              data1 := cdata1 |} cLog) =
      Ob~(Bits.single (interp_circuit (willFire_of_canFire' rwd cLog)) &&
          negb (Bits.single (interp_circuit (write1 cLog)))).
  Proof.
    t_interp_circuit_willFire_of_canFire.
  Qed.

  Arguments Circuits.willFire_of_canFire' : simpl never.

  Lemma interp_circuit_willFire_of_canFire'_mux_rwdata:
    forall (idx : reg_t) s (rwd1 rwd2 : rwdata (R idx)) (cCond : circuit 1) (rwdL : rwdata (R idx)),
      interp_circuit (willFire_of_canFire' (mux_rwdata s cCond rwd1 rwd2) rwdL) =
      if Bits.single (interp_circuit cCond) then
        interp_circuit (willFire_of_canFire' rwd1 rwdL)
      else
        interp_circuit (willFire_of_canFire' rwd2 rwdL).
  Proof.
    intros *;
      unfold willFire_of_canFire'; cbn.
    repeat (rewrite !lco_proof; cbn).
    destruct (interp_circuit cCond) as [ [ | ] [ ] ];
      cbn; eauto.
  Qed.

  (* Hint Extern 1 => eapply circuit_gamma_equiv_CtxCons : circuits. *)

  Hint Resolve
       circuit_lt_CAnnot_l
       circuit_lt_CAnnot_r
       circuit_lt_CBundleRef_l
       circuit_lt_CBundleRef_r
       circuit_lt_CAnd
       circuit_lt_CAnd_l
       circuit_lt_CAnd_r
       circuit_lt_opt_l
       circuit_lt_opt_r
       circuit_lt_COr
       circuit_lt_CNot
       circuit_lt_true
       circuit_lt_false
       circuit_lt_refl
       circuit_lt_true
       circuit_lt_false
       rwset_circuit_lt_invariant_putenv
       rwset_circuit_lt_invariant_refl : circuits.
  Hint Resolve Bits.single_inj : circuits.
  Hint Extern 3 => cbn in * : circuits.
  Hint Extern 3 => red : circuits.

  Ltac t_step :=
    match goal with
    | _ => cleanup_step
    | _ => progress intros
    | _ => progress cbn in *
    | [ H: context[lco_fn] |- _ ] => rewrite lco_proof in H
    | [  |- context[lco_fn] ] => rewrite lco_proof
    | [ H: _ * _ |- _ ] => destruct H
    | [ H: _ \/ _ |- _ ] => destruct H
    | [ H: exists _, _ |- _ ] => destruct H
    | [  |- Ob~_ = Ob~_ ] => f_equal
    | [ H: ?x = true |- context[?x] ] => rewrite H
    | [ H: ?x = false |- context[?x] ] => rewrite H
    | [ H: interp_circuit ?c = Ob~_ |- context[interp_circuit ?c] ] =>
      rewrite H
    | [ |- match (if ?x then _ else _) with _ => _ end ] =>
      destruct x eqn:?; cbn
    | [ |- context[Circuits.compile_action ?lco ?rc ?gamma ?ex ?clog] ] =>
      destruct (Circuits.compile_action lco rc gamma ex clog) eqn:?; cbn
    | [ IH: context[interp_action _ _ _ _ _ ?ex]  |-
        context[interp_action _ _ ?Gamma ?Log ?log ?ex] ] =>
      specialize (IH _ Gamma _ log ltac:(ceauto) ltac:(ceauto) ltac:(ceauto)
                     ltac:(ceauto) ltac:(eauto using circuit_gamma_equiv_CtxCons with circuits)
                     ltac:(ceauto) ltac:(ceauto));
      cbv zeta in IH;
      destruct (interp_action _ _ Gamma Log log ex) as [(? & ?) | ] eqn:?; cbn
    | [ H: interp_circuit ?x = bits_of_value _ |- context[interp_circuit ?x] ] =>
      rewrite H
    | [  |- context[REnv.(getenv) (map2 REnv _ _ _)] ] =>
      rewrite getenv_map2
    | [ Heq: Circuits.compile_action ?lco ?rc ?gamma ?ex ?clog = _  |- _ ] => progress rewrite Heq in *
    end.

  (* Create HintDb circuits discriminated. *)
  Ltac t := repeat t_step; eauto 6.  (* with circuits. *)

  Ltac interp_willFire_cleanup :=
    repeat match goal with
           | _ => reflexivity
           (* The notations for willFire_of_canFire and willFire_of_canFire'
              can't be used here, because of section variable (Coq bug?) *)
           | [ H: interp_circuit (Circuits.willFire_of_canFire _ _ _) = Ob~1 |- _ ] =>
             rewrite interp_willFire_of_canFire_true in H
           | [ H: interp_circuit (Circuits.willFire_of_canFire _ _ _) = Ob~0 |- _ ] =>
             rewrite interp_willFire_of_canFire_false in H
           | [ |- interp_circuit (Circuits.willFire_of_canFire _ _ _) = Ob~1 ] =>
             rewrite interp_willFire_of_canFire_true
           | [ |- interp_circuit (Circuits.willFire_of_canFire _ _ _) = Ob~0 ] =>
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
           | [  |- interp_circuit (Circuits.willFire_of_canFire' _ _ _) = Ob~_ ] =>
             (rewrite interp_circuit_willFire_of_canFire_read0 ||
              rewrite interp_circuit_willFire_of_canFire_read1 ||
              rewrite interp_circuit_willFire_of_canFire_write0 ||
              rewrite interp_circuit_willFire_of_canFire_write1);
             [ .. | solve[cbn; rewrite ?lco_proof; intuition eauto] ]
           | [ H: context[interp_circuit _ = _] |-
               context[interp_circuit _] ] =>
             rewrite H
           | _ => progress rewrite ?negb_true_iff, ?negb_false_iff
           end; cbn.

  Ltac may_read_write_t :=
    unfold may_read0, may_read1, may_write in *;
    repeat match goal with
           | _ => rewrite lco_proof in *
           | _ => progress bool_cleanup
           | [ H: log_rwdata_consistent _ ?regs |-
               context [Bits.single (interp_circuit (_ (REnv.(getenv) ?regs ?idx)))] ] =>
             specialize (H idx); cbv zeta in *; repeat cleanup_step
           end.

  Lemma circuit_gamma_equiv_CtxCons_rev {sig}:
    forall (k: var_t) (tau: type) (Gamma: vcontext sig) (gamma: ccontext sig) v (c: circuit tau),
      circuit_gamma_equiv (CtxCons (k, tau) v Gamma) (CtxCons (k, tau) c gamma) ->
      circuit_gamma_equiv Gamma gamma.
  Proof.
    unfold circuit_gamma_equiv.
    intros * Heq **; apply (Heq _ _ (MemberTl (k0, tau0) (k, tau) sig m)).
  Qed.

  Lemma circuit_gamma_equiv_ctl {sig}:
    forall (k: var_t) (tau: type) (Gamma: vcontext ((k, tau) :: sig)) (gamma: ccontext ((k, tau) :: sig)),
      circuit_gamma_equiv Gamma gamma ->
      circuit_gamma_equiv (ctl Gamma) (ctl gamma).
  Proof.
    intros * Heq; eapply circuit_gamma_equiv_CtxCons_rev.
    rewrite (ceqn Gamma), (ceqn gamma) in Heq; eassumption.
  Qed.

  Lemma circuit_gamma_equiv_creplace:
    forall (sig : tsig var_t) (k : var_t) (tau : type)
      (m : member (k, tau) sig) (vGamma : vcontext sig)
      (a : action_circuit R Sigma REnv tau) (cGamma : ccontext sig) t,
      interp_circuit (retVal a) = bits_of_value t ->
      circuit_gamma_equiv vGamma cGamma -> circuit_gamma_equiv (creplace m t vGamma) (creplace m (retVal a) cGamma).
  Proof.
    unfold circuit_gamma_equiv; induction sig; intros.
    - destruct (mdestruct m).
    - destruct (eq_dec k0 k), (eq_dec tau0 tau); subst;
        try destruct (eq_dec m m0); subst.
      all: rewrite ?cassoc_creplace_eq, ?cassoc_creplace_neq,
           ?cassoc_creplace_neq_members by congruence;
        eauto.
  Qed.

  Definition ccontext_equiv {sig} (c0 c1 : ccontext sig) :=
    forall (k: var_t) (tau: type) (m: member (k, tau) sig),
      interp_circuit (cassoc m c0) = interp_circuit (cassoc m c1).

  Lemma ccontext_equiv_sym {sig}:
    forall (c0 c1: ccontext sig), ccontext_equiv c0 c1 <-> ccontext_equiv c1 c0.
  Proof. firstorder. Qed.

  Lemma ccontext_equiv_refl {sig}:
    forall (c: ccontext sig), ccontext_equiv c c.
  Proof. firstorder. Qed.

  Lemma ccontext_equiv_cons {sig}:
    forall k tau (c0 c1: circuit _) (ctx0 ctx1: ccontext sig),
      ccontext_equiv ctx0 ctx1 ->
      interp_circuit c0 = interp_circuit c1 ->
      ccontext_equiv (CtxCons (k, tau) c0 ctx0) (CtxCons (k, tau) c1 ctx1).
  Proof.
    unfold ccontext_equiv; intros.
    destruct (mdestruct m) as [(Heq & ->) | (m' & ->)]; cbn.
    inversion Heq; subst; rewrite <- Eqdep_dec.eq_rect_eq_dec by apply eq_dec; cbn.
    all: eauto.
  Qed.

  Lemma circuit_gamma_equiv_ccontext_equiv {sig}:
    forall (c0 c1: ccontext sig) (v: vcontext sig),
      ccontext_equiv c0 c1 ->
      circuit_gamma_equiv v c0 ->
      circuit_gamma_equiv v c1.
  Proof.
    unfold circuit_gamma_equiv, ccontext_equiv; intros * Hcceq Hgammaeq **.
    rewrite <- Hcceq, <- Hgammaeq; reflexivity.
  Qed.

  Lemma ccontext_equiv_mux_ccontext {sig}:
    forall (cond: circuit 1) (c0 c1: ccontext sig),
      ccontext_equiv (if Bits.single (interp_circuit cond) then c0 else c1)
                     (mux_ccontext cond c0 c1).
  Proof.
    induction sig as [ | (k, tau) sig ]; cbn; intros;
      rewrite (ceqn c0), (ceqn c1).
    - destruct Bits.single; apply ccontext_equiv_refl.
    - specialize (IHsig cond (ctl c0) (ctl c1)).
      destruct Bits.single eqn:Heq; cbn;
        apply ccontext_equiv_cons; cbn; try rewrite Heq.
      all: eauto.
  Qed.

  Lemma mux_gamma_equiv_t:
    forall (sig : tsig var_t) (cond: circuit 1),
      Bits.single (interp_circuit cond) = true ->
      forall (v0 : vcontext sig) (c0 c1 : ccontext sig),
        circuit_gamma_equiv v0 c0 ->
        circuit_gamma_equiv v0 (mux_ccontext cond c0 c1).
  Proof.
    intros * Heq **.
    eapply circuit_gamma_equiv_ccontext_equiv;
      [ apply ccontext_equiv_mux_ccontext | ].
    rewrite Heq; assumption.
  Qed.

  Lemma mux_gamma_equiv_f:
    forall (sig : tsig var_t) (cond: circuit 1),
      Bits.single (interp_circuit cond) = false ->
      forall (v0 : vcontext sig) (c0 c1 : ccontext sig),
        circuit_gamma_equiv v0 c1 ->
        circuit_gamma_equiv v0 (mux_ccontext cond c0 c1).
  Proof.
    intros * Heq **.
    eapply circuit_gamma_equiv_ccontext_equiv;
      [ apply ccontext_equiv_mux_ccontext | ].
    rewrite Heq; assumption.
  Qed.

  Theorem action_compiler_correct {sig tau} Log cLog:
    forall (ex: action sig tau) (clog: rwcircuit)
      (Gamma: vcontext sig) (gamma: ccontext sig) log,
      log_rwdata_consistent log clog.(regs) ->
      log_rwdata_consistent Log cLog ->
      log_data0_consistent log Log clog.(regs) ->
      log_data1_consistent log Log clog.(regs) ->
      circuit_gamma_equiv Gamma gamma ->
      circuit_env_equiv ->
      interp_circuit (willFire_of_canFire clog cLog) = Ob~1 ->
      let (cExpr, gamma_new) := compile_action rc gamma ex clog in
      match interp_action r sigma Gamma Log log ex with
      | Some (l', v, Gamma_new) =>
        interp_circuit cExpr.(retVal) = bits_of_value v /\
        log_rwdata_consistent l' cExpr.(erwc).(regs) /\
        log_data0_consistent l' Log cExpr.(erwc).(regs) /\
        log_data1_consistent l' Log cExpr.(erwc).(regs) /\
        interp_circuit (willFire_of_canFire cExpr.(erwc) cLog) = Ob~1 /\
        circuit_gamma_equiv Gamma_new gamma_new (* 6 > 5 :( for eauto *)
      | None =>
        interp_circuit (willFire_of_canFire cExpr.(erwc) cLog) = Ob~0
      end.
  Proof.
    induction ex; intros.
    - (* Fail *) t; interp_willFire_cleanup; t.
    - (* Var *) cbn; rewrite lco_proof; eauto 6.
    - (* Const *) cbn; rewrite lco_proof; eauto 6.
    - (* Assign *)
      t; interp_willFire_cleanup; t; eauto using circuit_gamma_equiv_creplace.
    - (* Seq *)
      t.
      eapply interp_circuit_circuit_lt_helper_false;
        eauto using action_compile_willFire_of_canFire_decreasing.
    - (* Bind *)
      t. eauto 7 using circuit_gamma_equiv_ctl.
      eapply interp_circuit_circuit_lt_helper_false;
        eauto using action_compile_willFire_of_canFire_decreasing.
    - (* If *)
      t.
      + repeat apply conj; try reflexivity.
        * apply log_rwdata_consistent_mux_l;
            eauto with circuits.
        * apply log_data0_consistent_mux_l;
            eauto with circuits.
        * apply log_data1_consistent'_mux_l;
            eauto with circuits.
        * unfold mux_rwsets; interp_willFire_cleanup; t.
          rewrite (interp_circuit_willFire_of_canFire'_mux_rwdata idx); t.
        * eauto using mux_gamma_equiv_t.
      + unfold mux_rwsets; interp_willFire_cleanup; t.
        right. exists x; t.
        rewrite (interp_circuit_willFire_of_canFire'_mux_rwdata x); t.
      + repeat apply conj; try reflexivity.
        * apply log_rwdata_consistent_mux_r;
            eauto with circuits.
        * apply log_data0_consistent_mux_r;
            eauto with circuits.
        * apply log_data1_consistent'_mux_r;
            eauto with circuits.
        * unfold mux_rwsets; interp_willFire_cleanup; t.
          rewrite (interp_circuit_willFire_of_canFire'_mux_rwdata idx); t.
        * eauto using mux_gamma_equiv_f.
      + unfold mux_rwsets; interp_willFire_cleanup; t.
        right; exists x; t.
        rewrite (interp_circuit_willFire_of_canFire'_mux_rwdata x); t.
      + unfold mux_rwsets; interp_willFire_cleanup; t.
        * left.
          destruct Bits.single;
            eapply interp_circuit_circuit_lt_helper_false;
            try eapply rwset_circuit_lt_compile_action_correct;
            eauto.
        * right.
          exists x; t.
          rewrite (interp_circuit_willFire_of_canFire'_mux_rwdata x); t.
          destruct Bits.single; t;
            eapply interp_circuit_circuit_lt_helper_false;
            try eapply action_compile_willFire_of_canFire'_decreasing;
            eauto.
    - (* Read *)
      destruct port.
      + cbn.
        destruct (may_read0 Log log idx) eqn:?; cbn.
        * repeat eapply conj.
          -- rewrite lco_proof; eauto.
          -- apply log_rwdata_consistent_log_cons_putenv;
               [ eauto | red ]; cbn; rewrite ?Bits.single_cons, lco_proof; eauto.
          -- apply log_data0_consistent_putenv_read_write1; eauto.
          -- apply log_data1_consistent_putenv_read_write0; eauto.
          -- interp_willFire_cleanup;
               may_read_write_t.
          -- intuition.
        * interp_willFire_cleanup.
          may_read_write_t.
          right; exists idx;
            interp_willFire_cleanup;
            may_read_write_t.
          eauto.
          right; exists idx;
            interp_willFire_cleanup;
            may_read_write_t.
      + cbn.
        destruct (may_read1 Log idx) eqn:?; cbn.
        * repeat eapply conj.
          -- apply H1.
          -- apply log_rwdata_consistent_log_cons_putenv;
               [ eauto | red ]; cbn; rewrite ?Bits.single_cons, lco_proof; eauto.
          -- apply log_data0_consistent_putenv_read_write1; eauto.
          -- apply log_data1_consistent_putenv_read_write0; eauto.
          -- interp_willFire_cleanup;
               may_read_write_t.
          -- intuition.
        * interp_willFire_cleanup.
          right.
          eexists.
          interp_willFire_cleanup.
          may_read_write_t.
    - (* Write *)
      destruct port; t.
      + repeat apply conj.
        * interp_willFire_cleanup; may_read_write_t.
        * (apply log_rwdata_consistent_log_cons_putenv;
             [ eauto | red ]; cbn; rewrite ?Bits.single_cons, lco_proof; eauto).
        * apply log_data0_consistent_putenv_write0; eauto.
        * apply log_data1_consistent_putenv_read_write0; eauto.
        * interp_willFire_cleanup;
              may_read_write_t.
        * trivial.
      + interp_willFire_cleanup;
            may_read_write_t; eauto.
        * right; exists idx; interp_willFire_cleanup;
            may_read_write_t.
        * right; exists idx; interp_willFire_cleanup;
            may_read_write_t.
        * right; exists idx; interp_willFire_cleanup;
            may_read_write_t.
      + eapply interp_circuit_circuit_lt_helper_false; eauto;
          intros; apply circuit_lt_willFire_of_canFire; cbn;
            eauto 6 with circuits.
        all: intros;
          apply rwset_circuit_lt_invariant_putenv;
          eauto 8 with circuits.
      + repeat apply conj.
        * interp_willFire_cleanup;
            may_read_write_t.
        * (apply log_rwdata_consistent_log_cons_putenv;
             [ eauto | red ]; cbn; rewrite ?Bits.single_cons, lco_proof; eauto).
        * apply log_data0_consistent_putenv_read_write1; eauto.
        * apply log_data1_consistent_putenv_write1; eauto.
        * interp_willFire_cleanup;
            may_read_write_t.
        * trivial.
      + interp_willFire_cleanup;
          may_read_write_t; eauto.
        right; exists idx; interp_willFire_cleanup;
          may_read_write_t.
      + eapply interp_circuit_circuit_lt_helper_false; eauto;
          intros; apply circuit_lt_willFire_of_canFire; cbn;
            eauto 4 with circuits.
        all: intros;
          apply rwset_circuit_lt_invariant_putenv;
          eauto 8 with circuits.
    - (* Unop *)
      t; eauto 7 using compile_unop_correct.
    - (* Binop *)
      t; eauto 7 using compile_binop_correct,
         interp_circuit_circuit_lt_helper_false,
         action_compile_willFire_of_canFire_decreasing.
    - (* ExternalCall *)
      t; eauto 7 using interp_circuit_circuit_lt_helper_false,
         action_compile_willFire_of_canFire_decreasing.
    - (* APos *) t.
  Qed.

  Arguments update_accumulated_rwset : simpl never.
  Notation update_accumulated_rwset := (update_accumulated_rwset lco).

  Lemma log_rwdata_consistent_update_accumulated_rwset:
    forall (l : Log) (l' : rwset) (L : Log) (L' : rwset),
      log_rwdata_consistent L L' ->
      log_rwdata_consistent l l' ->
      log_rwdata_consistent (log_app l L) (update_accumulated_rwset l' L').
  Proof.
    unfold log_rwdata_consistent, update_accumulated_rwset; intros * HL Hl ** ;
      rewrite getenv_map2; cbn.
    specialize (HL idx); specialize (Hl idx);
      repeat (rewrite !lco_proof || bool_cleanup || rewrite log_existsb_app);
      eauto.
  Qed.

  Lemma log_data0_consistent'_update_accumulated:
    forall (Log : Log) (cLog : rwset) (l : CompilerCorrectness.Log) (rws : rwset),
      log_data0_consistent l Log rws ->
      log_data0_consistent' (log_app l Log) (update_accumulated_rwset rws cLog).
  Proof.
    unfold log_data0_consistent, log_data0_consistent', update_accumulated_rwset; intros * Hl ** ;
      rewrite getenv_map2; cbn;
        eauto.
  Qed.

  Lemma log_data1_consistent'_update_accumulated:
    forall (cLog : rwset) (l L: Log) (rws : rwset),
      log_data1_consistent l L rws ->
      (* log_data1_consistent' L cLog -> *)
      log_rwdata_consistent l rws ->
      (* log_rwdata_consistent L cLog -> *)
      log_data1_consistent' (log_app l L) (update_accumulated_rwset rws cLog).
  Proof.
    unfold log_data1_consistent', update_accumulated_rwset; intros * Hl (* HL Hcl HcL *) Hrw idx H;
      rewrite getenv_map2; cbn.
    repeat match goal with
           | _ => cleanup_step
           | _ => progress cbv zeta in *
           | [ H: ?x || ?y = true -> _ |- _ ] =>
             destruct x eqn:?, y eqn:?; cbn in H; try discriminate; specialize (H eq_refl)
           | [ H: log_data1_consistent _ _ _, idx: reg_t |- _ ] => specialize (H idx)
           | [ H: log_rwdata_consistent _ _, idx: reg_t |- _ ] => specialize (H idx)
           | [ H: context[log_existsb (log_app _ _) _ _] |- _ ] => rewrite log_existsb_app in H
           | [ H: _ = _ |- _ ] => rewrite H
           end; eauto.
  Qed.

  Notation adapter := (adapter lco).

  Lemma log_rwdata_consistent_empty_adapter cLog :
    log_rwdata_consistent log_empty (regs (adapter cLog)).
  Proof.
    red; intros; cbn.
    rewrite getenv_map; cbn.
    rewrite !log_existsb_empty, lco_proof; auto.
  Qed.

  Lemma log_data0_consistent_empty_adapter Log cLog:
    log_data0_consistent' Log cLog ->
    log_data0_consistent log_empty Log (regs (adapter cLog)).
  Proof.
    red; unfold log_data0_consistent'; intros; cbn.
    rewrite getenv_map; cbn.
    rewrite log_app_empty_r.
    eauto.
  Qed.

  Lemma log_data1_consistent_empty_adapter Log cLog:
    log_data1_consistent' Log cLog ->
    log_data1_consistent log_empty Log (regs (adapter cLog)).
  Proof.
    red; unfold log_data1_consistent'; intros * Hcst idx Hex; cbn.
    rewrite getenv_map; cbn.
    specialize (Hcst idx).
    rewrite log_app_empty_r.
    rewrite log_app_empty_r in Hex.
    intuition eauto.
  Qed.

  Lemma interp_circuit_willFire_of_canFire_adapter (cLog: REnv.(env_t) _):
    interp_circuit (willFire_of_canFire (adapter cLog) cLog) = Ob~1.
  Proof.
    interp_willFire_cleanup.
    - rewrite lco_proof; reflexivity.
    - rewrite getenv_map.
      unfold Circuits.willFire_of_canFire'.
      t_interp_circuit_willFire_of_canFire.
  Qed.

  Hint Resolve circuit_gamma_equiv_empty : circuits.
  Hint Resolve log_data0_consistent_empty_adapter : circuits.
  Hint Resolve log_data1_consistent_empty_adapter : circuits.
  Hint Resolve log_rwdata_consistent_empty_adapter : circuits.
  Hint Resolve interp_circuit_willFire_of_canFire_adapter : circuits.
  Hint Resolve log_rwdata_consistent_update_accumulated_rwset : circuits.
  Hint Resolve log_data0_consistent'_update_accumulated : circuits.
  Hint Resolve log_data1_consistent'_update_accumulated : circuits.

  Hint Resolve log_data0_consistent'_mux_l : circuits.
  Hint Resolve log_data1_consistent'_mux_l : circuits.
  Hint Resolve log_rwdata_consistent_mux_l : circuits.
  Hint Resolve log_data0_consistent'_mux_r : circuits.
  Hint Resolve log_data1_consistent'_mux_r : circuits.
  Hint Resolve log_rwdata_consistent_mux_r : circuits.

  Hint Resolve compile_unop_correct : circuits.
  Hint Resolve compile_binop_correct : circuits.

  Notation scheduler := (scheduler pos_t rule_name_t).
  Context (rules: rule_name_t -> rule).

  Notation compile_scheduler_circuit := (compile_scheduler_circuit lco).
  Notation compile_scheduler' := (compile_scheduler' lco).

  Lemma interp_circuit_willFire_of_canFire_remove_bundle' :
    forall (cLog: rwset) (c: rwcircuit) rl rs bundle,
        interp_circuit
          (Circuits.willFire_of_canFire lco (bundleref_wrap_erwc rl rs bundle c) cLog) =
        interp_circuit
          (Circuits.willFire_of_canFire (REnv := REnv) lco c cLog) .
  Proof.
    unfold bundleref_wrap_erwc; intros.
    rewrite !interp_willFire_of_canFire_eqn; cbn.
    do 2 f_equal.
    apply forallb_pointwise; intros.
    unfold willFire_of_canFire', bundleref_wrap_rwset.
    rewrite getenv_map.
    repeat (cbn; rewrite !lco_proof); reflexivity.
  Qed.

  Lemma interp_circuit_willFire_of_canFire_remove_bundle :
    forall (cLog: rwset) (c: rwcircuit) rl rs bundle res,
      interp_circuit
        ((Circuits.willFire_of_canFire (REnv := REnv) lco c) cLog) = res ->
      interp_circuit
        (Circuits.willFire_of_canFire lco (bundleref_wrap_erwc rl rs bundle c) cLog) = res.
  Proof.
    intros; subst; apply interp_circuit_willFire_of_canFire_remove_bundle'.
  Qed.

  Ltac bundle_t :=
    repeat match goal with
           | [ H: context[(getenv ?REnv (map2 ?REnv ?f2 ?f3 ?cLog) ?idx)] |- _ ] =>
             rewrite @getenv_map2 in H
           | [ H: context[(getenv ?REnv (map ?REnv ?f2 ?cLog) ?idx)] |- _ ] =>
             rewrite @getenv_map in H
           | [ |- context[(getenv ?REnv (map2 ?REnv ?f2 ?f3 ?cLog) ?idx)] ] =>
             rewrite @getenv_map2
           | [ |- context[(getenv ?REnv (map ?REnv ?f2 ?cLog) ?idx)] ] =>
             rewrite @getenv_map
           | [ |- context[match (?ind) with _ => _ end] ] => destruct ind
           end; eauto.

  Lemma log_data1_consistent'_bundle_equiv : forall Log cLog regs rl rs bundle,
      log_data1_consistent'
        Log (Circuits.update_accumulated_rwset lco regs cLog) <->
      log_data1_consistent'
        Log (Circuits.update_accumulated_rwset lco (bundleref_wrap_rwset rl rs bundle regs) cLog).
  Proof.
    unfold log_data1_consistent', bundleref_wrap_rwset, update_accumulated_rwset;
      split; intros H idx; specialize (H idx);
        bundle_t.
  Qed.

  Lemma log_data0_consistent'_bundle_equiv : forall Log cLog regs rl rs bundle,
      log_data0_consistent'
        Log (Circuits.update_accumulated_rwset lco regs cLog) <->
      log_data0_consistent'
        Log (Circuits.update_accumulated_rwset lco (bundleref_wrap_rwset rl rs bundle regs) cLog).
  Proof.
    unfold log_data0_consistent', bundleref_wrap_rwset, update_accumulated_rwset;
      split; intros H idx; specialize (H idx);
        bundle_t.
  Qed.

  Lemma log_rwdata_consistent_bundle_equiv : forall Log regs rl rs bundle,
      log_rwdata_consistent Log regs <->
      log_rwdata_consistent Log (bundleref_wrap_rwset rl rs bundle regs).
  Proof.
    unfold log_rwdata_consistent, bundleref_wrap_rwset;
      split; intros H idx; specialize (H idx);
        bundle_t.
  Qed.

  Lemma log_data1_consistent'_bundle_elim : forall Log cLog regs rl rs bundle,
      log_data1_consistent'
        Log (Circuits.update_accumulated_rwset lco regs cLog) ->
      log_data1_consistent'
        Log (Circuits.update_accumulated_rwset lco (bundleref_wrap_rwset rl rs bundle regs) cLog).
  Proof.
    apply log_data1_consistent'_bundle_equiv.
  Qed.

  Lemma log_data0_consistent'_bundle_elim : forall Log cLog regs rl rs bundle,
      log_data0_consistent'
        Log (Circuits.update_accumulated_rwset lco regs cLog) ->
      log_data0_consistent'
        Log (Circuits.update_accumulated_rwset lco (bundleref_wrap_rwset rl rs bundle regs) cLog).
  Proof.
    apply log_data0_consistent'_bundle_equiv.
  Qed.

  Lemma log_rwdata_consistent_bundle_elim : forall Log regs rl rs bundle,
      log_rwdata_consistent Log regs ->
      log_rwdata_consistent Log (bundleref_wrap_rwset rl rs bundle regs).
  Proof.
    apply log_rwdata_consistent_bundle_equiv.
  Qed.

  Hint Resolve log_data1_consistent'_bundle_elim : circuits.
  Hint Resolve log_data0_consistent'_bundle_elim : circuits.
  Hint Resolve log_rwdata_consistent_bundle_elim : circuits.
  Hint Resolve interp_circuit_willFire_of_canFire_remove_bundle : circuits.

  Theorem compile_scheduler_circuit_correct:
    forall (s: scheduler) Log cLog,
      log_data1_consistent' Log cLog ->
      log_data0_consistent' Log cLog ->
      log_rwdata_consistent Log cLog ->
      circuit_env_equiv ->
      log_data1_consistent' (interp_scheduler' r sigma rules Log s) (compile_scheduler_circuit rc rules s cLog) /\
      log_data0_consistent' (interp_scheduler' r sigma rules Log s) (compile_scheduler_circuit rc rules s cLog) /\
      log_rwdata_consistent (interp_scheduler' r sigma rules Log s) (compile_scheduler_circuit rc rules s cLog).
  Proof.
    induction s; cbn; intros.
    - eauto.
    - pose proof (@action_compiler_correct nil _ Log cLog (rules r0)) as Hrc.
      unshelve eassert (Hrc := Hrc (adapter cLog) CtxEmpty CtxEmpty log_empty
                                  ltac:(ceauto) ltac:(ceauto)
                                  ltac:(ceauto) ltac:(ceauto)
                                  ltac:(ceauto) ltac:(ceauto)
                                                ltac:(ceauto)).
      destruct (interp_action r sigma CtxEmpty Log log_empty (rules r0)) as [((? & ?) & ?) | ] eqn:? ;
        destruct compile_action; cbn; apply IHs;
          repeat cleanup_step; eauto with circuits.
    - pose proof (@action_compiler_correct nil _ Log cLog (rules r0)) as Hrc.
      unshelve eassert (Hrc := Hrc (adapter cLog) CtxEmpty CtxEmpty log_empty
                                  ltac:(ceauto) ltac:(ceauto)
                                  ltac:(ceauto) ltac:(ceauto)
                                  ltac:(ceauto) ltac:(ceauto)
                                  ltac:(ceauto)).
      destruct (interp_action r sigma CtxEmpty Log log_empty (rules r0)) as [(? & ?) | ] eqn:?; cbn; t.
      + repeat apply conj.
        * apply log_data1_consistent'_mux_l; try apply IHs1; ceauto.
        * apply log_data0_consistent'_mux_l; try apply IHs1; ceauto.
        * apply log_rwdata_consistent_mux_l; try apply IHs1; ceauto.
      + repeat apply conj.
        * apply log_data1_consistent'_mux_r; try apply IHs2; ceauto.
        * apply log_data0_consistent'_mux_r; try apply IHs2; ceauto.
        * apply log_rwdata_consistent_mux_r; try apply IHs2; ceauto.
    - eauto.
  Qed.

  Notation init_scheduler_circuit := (init_scheduler_circuit lco).

  Lemma log_rwdata_consistent_empty_init_scheduler:
    log_rwdata_consistent log_empty (init_scheduler_circuit rc).
  Proof.
    red; unfold init_scheduler_circuit, init_scheduler_rwdata;
      intros; rewrite !getenv_create, !log_existsb_empty; cbn;
        rewrite lco_proof; eauto.
  Qed.

  Lemma log_data0_consistent'_empty_init_scheduler:
    circuit_env_equiv ->
    log_data0_consistent' log_empty (init_scheduler_circuit rc).
  Proof.
    red; unfold init_scheduler_circuit, init_scheduler_rwdata, circuit_env_equiv;
      intros; rewrite !getenv_create; cbn;
        rewrite lco_proof, latest_write0_empty; eauto.
  Qed.

  Lemma log_data1_consistent'_empty_init_scheduler:
    log_data1_consistent' log_empty (init_scheduler_circuit rc).
  Proof.
    red; intros * H.
    rewrite log_existsb_empty in H; discriminate.
  Qed.

  Hint Resolve log_rwdata_consistent_empty_init_scheduler : circuits.
  Hint Resolve log_data0_consistent'_empty_init_scheduler : circuits.
  Hint Resolve log_data1_consistent'_empty_init_scheduler : circuits.

  Definition log_writes_ordered (l: Log) idx :=
    latest_write l idx =
    match latest_write1 l idx with
    | Some v => Some v
    | None => match latest_write0 l idx with
             | Some v => Some v
             | None => None
             end
    end.

  Theorem action_log_writes_ordered:
    forall sig tau a ctx Log log idx,
      log_writes_ordered (log_app log Log) idx ->
      match @interp_action pos_t var_t reg_t ext_fn_t R Sigma REnv r sigma sig tau ctx Log log a with
      | Some (l', _, _) => log_writes_ordered (log_app l' Log) idx
      | None => True
      end.
  Proof.
    induction a; cbn; intros; eauto;
      repeat match goal with
             | _ => progress cbn
             | [ IH: context[interp_action _ _ _ _ _ ?a]
                 |- context[interp_action ?r ?sigma ?ctx ?Log ?log ?a] ] =>
               specialize (IH ctx Log log _ ltac:(ceauto));
                 destruct (interp_action r sigma ctx Log log a) as [((? & ?) & ?) | ] eqn:?
             | [  |- match (if ?x then _ else _) with _ => _ end ] => destruct x eqn:?
             | _ => solve [eauto]
             end.
    - destruct port;
        [ destruct may_read0 | destruct may_read1 ]; cbn; eauto;
        unfold log_writes_ordered, log_cons in *;
        unfold latest_write, latest_write0, latest_write1, log_find in *;
        unfold log_app in *; rewrite !getenv_map2 in *;
          (destruct (eq_dec idx idx0); subst;
           [ rewrite !get_put_eq | rewrite !get_put_neq by eassumption ];
           [ |  ]); cbn;
            eauto.
    - destruct port;
        unfold log_writes_ordered, log_cons in *;
        unfold latest_write, latest_write0, latest_write1, log_find in *;
        unfold log_app in *; rewrite !getenv_map2 in *;
          (destruct (eq_dec idx idx0); subst;
           [ rewrite !get_put_eq | rewrite !get_put_neq by eassumption ];
           [ |  ]); cbn;
            eauto.
      may_read_write_t.
      rewrite list_find_opt_app.
      repeat setoid_rewrite latest_write1_None; eauto.
  Qed.

  Lemma log_writes_ordered_empty idx:
    log_writes_ordered (log_empty: Log) idx.
  Proof.
    unfold log_writes_ordered, log_cons;
      unfold latest_write, latest_write0, latest_write1, log_find, log_empty;
      rewrite !getenv_create; reflexivity.
  Qed.

  Hint Resolve log_writes_ordered_empty : circuits.

  Theorem scheduler_log_writes_ordered:
    forall s log idx,
      log_writes_ordered log idx ->
      log_writes_ordered (@interp_scheduler' pos_t var_t rule_name_t reg_t ext_fn_t R Sigma REnv r sigma rules log s) idx.
  Proof.
    induction s; cbn; intros; eauto.
    all: lazymatch goal with
         | [ |- context[interp_action ?r ?sigma ?ctx ?Log ?log ?rl] ] =>
           pose proof (action_log_writes_ordered _ _ rl ctx Log log _ ltac:(rewrite log_app_empty_r; ceauto));
             destruct (interp_action r sigma ctx Log log rl) as [((? & ?) & ?) | ] eqn:?
         end; eauto.
  Qed.

  Theorem compile_scheduler'_correct:
    forall (s: scheduler),
      circuit_env_equiv ->
      forall idx,
        interp_circuit (REnv.(getenv) (compile_scheduler' rc rules s) idx) =
        bits_of_value (REnv.(getenv) (commit_update r (interp_scheduler r sigma rules s)) idx).
  Proof.
    intros; unfold compile_scheduler', commit_update, commit_rwdata, interp_scheduler.
    rewrite !getenv_map2, !getenv_create; cbn.
    repeat (rewrite !lco_proof; cbn).
    pose proof (compile_scheduler_circuit_correct s log_empty (init_scheduler_circuit rc)
                                                  ltac:(ceauto) ltac:(ceauto)
                                                  ltac:(ceauto) ltac:(ceauto)) as (Hrv & Hcst0 & Hcst1).
    specialize (Hrv idx); specialize (Hcst0 idx); specialize (Hcst1 idx); cbv zeta in *.
    repeat cleanup_step.
    repeat bool_cleanup.

    rewrite scheduler_log_writes_ordered by ceauto.

    destruct (log_existsb _ _ is_write1) eqn:?; cbn.
    lazymatch goal with
    | [ H: _ -> match ?x with _ => _ end |- _ ] =>
      let Heq := fresh in
      specialize (H eq_refl); destruct x eqn:Heq; try (exfalso; eassumption);
        []; rewrite H
    end.

    reflexivity.
    rewrite latest_write1_None by eauto.
    destruct (log_existsb _ _ is_write0) eqn:?; cbn.
    - destruct latest_write0; eauto.
    - rewrite latest_write0_None; eauto.
  Qed.
End CompilerCorrectness.

Section CircuitInit.
  Context {pos_t var_t rule_name_t reg_t ext_fn_t: Type}.
  Context {eq_dec_var_t: EqDec var_t}.

  Context {R: reg_t -> type}.
  Context {Sigma: ext_fn_t -> ExternalSignature}.
  Context {REnv: Env reg_t}.

  Context (r: REnv.(env_t) R).
  Context (sigma: forall f, Sigma f).

  Lemma circuit_env_equiv_CReadRegister :
    forall (csigma: forall f, CSig_denote (CSigma_of_Sigma Sigma f)),
      csigma_spec sigma csigma ->
      circuit_env_equiv (rule_name_t := rule_name_t) r csigma (REnv.(create) CReadRegister).
  Proof.
    unfold circuit_env_equiv, cr_of_r; intros.
    rewrite getenv_create; cbn;
      rewrite getenv_map; cbn;
        reflexivity.
  Qed.
End CircuitInit.

Section Thm.
  Context {pos_t var_t rule_name_t reg_t ext_fn_t: Type}.
  Context {eq_dec_var_t: EqDec var_t}.

  Context {R: reg_t -> type}.
  Context {Sigma: ext_fn_t -> ExternalSignature}.
  Context {FiniteType_reg_t: FiniteType reg_t}.

  Context (r: ContextEnv.(env_t) R).
  Context (sigma: forall f, Sigma f).

  Context (s: scheduler pos_t rule_name_t).

  Section Standalone.
    Context (rules: rule_name_t -> rule pos_t var_t R Sigma).

    Theorem scheduler_compiler_correct:
      let spec_results := commit_update r (interp_scheduler r sigma rules s) in
      let circuits := compile_scheduler rules s in
      forall reg,
        interp_circuit (cr_of_r r) (csigma_of_sigma sigma) (ContextEnv.(getenv) circuits reg) =
        bits_of_value (ContextEnv.(getenv) spec_results reg).
    Proof.
      intros;
        unshelve eapply (compile_scheduler'_correct _ _ _ bool_simpl_lco);
        eauto using circuit_env_equiv_CReadRegister,
        csigma_spec_csigma_of_sigma.
    Qed.
  End Standalone.
End Thm.