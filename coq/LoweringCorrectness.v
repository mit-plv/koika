(*! Circuits | Proof of correctness for the lowering phase !*)
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Ring Coq.setoid_ring.Ring.
Require Import Koika.Common Koika.Environments Koika.Syntax
        Koika.SemanticProperties Koika.PrimitiveProperties Koika.Lowering.
Require Koika.TypedSemantics Koika.LoweredSemantics.

Section LoweringCorrectness.
  Context {pos_t var_t rule_name_t reg_t ext_fn_t: Type}.

  Context {R: reg_t -> type}.
  Context {Sigma: ext_fn_t -> ExternalSignature}.

  Notation CR := (lower_R R).
  Notation CSigma := (lower_Sigma Sigma).

  Context {REnv: Env reg_t}.
  Context (r: REnv.(env_t) R).
  Context (sigma: forall f, Sig_denote (Sigma f)).

  Notation lr := (lower_r r).
  Notation lsigma := (lower_sigma sigma).

  Lemma lower_r_eqn:
    forall idx, getenv REnv lr idx = bits_of_value (getenv REnv r idx).
  Proof.
    unfold lower_r; intros; rewrite getenv_map; reflexivity.
  Qed.

  Lemma lower_sigma_eqn:
    forall (fn : ext_fn_t) (v : arg1Sig (Sigma fn)),
      lsigma fn (bits_of_value v) = bits_of_value (sigma fn v).
  Proof.
    unfold lsigma; intros; rewrite value_of_bits_of_value; reflexivity.
  Qed.

  Notation taction := (TypedSyntax.action pos_t var_t R Sigma).
  Notation laction := (LoweredSyntax.action pos_t var_t CR CSigma).
  Notation tinterp := (TypedSemantics.interp_action r sigma).
  Notation linterp := (LoweredSemantics.interp_action lr lsigma).
  Notation tcontext := TypedSemantics.tcontext.
  Notation lcontext := LoweredSemantics.lcontext.
  Notation tlog := (Logs.Log R REnv).
  Notation llog := (Logs.CLog CR REnv).

  Context {var_t_eq_dec: EqDec var_t}.

  Ltac lower_op_t :=
    match goal with
    | _ => progress intros
    | _ => progress simpl in *
    | _ => progress unfold Bits.extend_beginning, Bits.extend_end,
          struct_sz, field_sz, array_sz, element_sz
    | _ => rewrite bits_of_value_of_bits
    | [ H: linterp _ _ _ _ = _ |- _ ] => rewrite H
    | [  |- context[match ?d with _ => _ end] ] => is_var d; destruct d
    | [  |- context[eq_rect _ _ _ _ ?pr] ] => destruct pr
    | [  |- Some (_, _, _) = Some (_, _, _) ] => repeat f_equal
    | [  |- Some _ = Some _ ] => f_equal
    | _ => (apply _eq_of_value ||
           apply _neq_of_value ||
           apply get_field_bits_slice ||
           apply subst_field_bits_slice_subst ||
           apply get_element_bits_slice ||
           apply subst_element_bits_slice_subst)
    | _ => rewrite sel_msb, vect_repeat_single_const
    | _ => solve [eauto]
    end.

  Ltac lower_op_correct_t :=
    repeat match goal with
           | _ => progress intros
           | [  |- context[match linterp _ _ _ ?a with _ => _ end] ] =>
             let v := fresh "v" in
             let Heq := fresh "Heq" in
             destruct (linterp _ _ _ a) as [((?, v), ?) | ] eqn:Heq; cbn;
             [ rewrite <- (bits_of_value_of_bits _ v) in Heq;
               remember (value_of_bits v) in *; clear dependent v | ]
           | [ fn: PrimTyped.fn1 |- _ ] => destruct fn; repeat lower_op_t
           | [ fn: PrimTyped.fn2 |- _ ] => destruct fn; repeat lower_op_t
           end.

  Theorem lower_unop_correct {sig lGamma lL ll}:
    forall fn (a: laction sig _),
      linterp lGamma lL ll (lower_unop fn a) =
      match linterp lGamma lL ll a with
      | Some (ll', bs, lGamma') =>
        let v := value_of_bits bs in
        Some (ll', bits_of_value (PrimSpecs.sigma1 fn v), lGamma')
      | None => None
      end.
  Proof.
    lower_op_correct_t.
  Qed.

  Theorem lower_binop_correct {sig lGamma lL ll}:
    forall fn (a1 a2: laction sig _),
      linterp lGamma lL ll (lower_binop fn a1 a2) =
      match linterp lGamma lL ll a1 with
      | Some (ll1, v1, lGamma1) =>
        match linterp lGamma1 lL ll1 a2 with
        | Some (ll2, v2, lGamma2) =>
          let v1 := value_of_bits v1 in
          let v2 := value_of_bits v2 in
          Some (ll2, bits_of_value (PrimSpecs.sigma2 fn v1 v2), lGamma2)
        | None => None
        end
      | None => None
      end.
  Proof.
    lower_op_correct_t.
  Qed.

  Definition context_equiv {sig}
             (tGamma: tcontext sig)
             (lGamma: lcontext (lsig_of_tsig sig)) :=
    lGamma = cmap (V := fun k_tau => type_denote (snd k_tau))
                  (V' := Bits.bits)
                  (fun k_tau => type_sz (@snd var_t type k_tau))
                  (fun _ v => bits_of_value v)
                  tGamma.

  Lemma context_equiv_cassoc {sig: tsig var_t} :
    forall (tGamma: tcontext sig)
      (lGamma: lcontext (lsig_of_tsig sig)),
      context_equiv tGamma lGamma ->
      forall {k tau} (m: member (k, tau) sig),
        cassoc (lower_member m) lGamma =
        bits_of_value (cassoc m tGamma).
  Proof.
    intros * -> *.
    rewrite <- (cmap_cassoc _ (fun _ v => bits_of_value v) _ m); reflexivity.
  Qed.

  Lemma context_equiv_creplace:
    forall {sig: tsig var_t} {k: var_t} {tau: type}
      (m: member (k, tau) sig) (v: tau)
      (tGamma: tcontext sig)
      (lGamma: lcontext (lsig_of_tsig sig)),
      context_equiv tGamma lGamma ->
      context_equiv
        (creplace m v tGamma)
        (creplace (lower_member m) (bits_of_value v) lGamma).
  Proof.
    unfold context_equiv, lower_member; intros * ->.
    rewrite cmap_creplace; reflexivity.
  Qed.

  Lemma context_equiv_CtxCons:
    forall (sig: tsig var_t) (tau: type) (k: var_t) (v: tau)
      (tGamma: tcontext sig) (lGamma: lcontext (lsig_of_tsig sig)),
      context_equiv tGamma lGamma ->
      context_equiv (CtxCons (k, tau) v tGamma)
                    (CtxCons (type_sz tau) (bits_of_value v) lGamma).
  Proof.
    unfold context_equiv; intros * ->; reflexivity.
  Qed.

  Lemma context_equiv_ctl:
    forall (sig: tsig var_t) (tau: type) (k: var_t)
      (tGamma: tcontext ((k, tau) :: sig))
      (lGamma: lcontext (lsig_of_tsig ((k, tau) :: sig))),
      context_equiv tGamma lGamma ->
      context_equiv (ctl tGamma) (ctl lGamma).
  Proof.
    unfold context_equiv; intros * ->.
    rewrite cmap_ctl; reflexivity.
  Qed.

  Definition log_equiv (tL: tlog) (lL: llog) : Prop :=
    lL = Logs.log_map (fun k l => Logs.RLog_map bits_of_value l) tL.

  Lemma log_equiv_may_read:
    forall (tL: tlog) (lL: llog),
      log_equiv tL lL ->
      forall (port: Port) (idx: reg_t),
        Logs.may_read tL port idx = Logs.may_read lL port idx.
  Proof. intros * -> *; symmetry; apply may_read_map_values. Qed.

  Lemma log_equiv_may_write:
    forall (tL tl: tlog) (lL ll: llog),
      log_equiv tL lL ->
      log_equiv tl ll ->
      forall (port: Port) (idx: reg_t),
        Logs.may_write tL tl port idx = Logs.may_write lL ll port idx.
  Proof. intros * -> -> *; symmetry; apply may_write_map_values. Qed.

  Lemma log_equiv_cons:
    forall (tL: tlog) (lL: llog),
      log_equiv tL lL ->
      forall idx tle lle,
        lle = LogEntry_map bits_of_value tle ->
        log_equiv (log_cons idx tle tL) (log_cons idx lle lL).
  Proof.
    intros * -> * ->.
    apply equiv_eq; intro.
    unfold log_equiv, log_cons, log_map.
    rewrite !getenv_map.
    destruct (eq_dec (EqDec := EqDec_FiniteType (FT := REnv.(finite_keys))) k idx); subst.
    - rewrite !get_put_eq; reflexivity.
    - rewrite !get_put_neq, !getenv_map; congruence.
  Qed.

  Lemma log_equiv_latest_write0:
    forall (tl: tlog) (ll: llog),
      log_equiv tl ll ->
      forall idx,
        latest_write0 ll idx =
        match latest_write0 tl idx with
        | Some v => Some (bits_of_value v)
        | None => None
        end.
  Proof.
    intros * -> *.
    setoid_rewrite latest_write0_map_values; reflexivity.
  Qed.

  Create HintDb lowering.
  Hint Resolve lower_r_eqn : lowering.
  Hint Extern 1 => apply lower_sigma_eqn : lowering.

  Hint Resolve context_equiv_cassoc : lowering.
  Hint Resolve context_equiv_creplace : lowering.
  Hint Resolve context_equiv_CtxCons : lowering.
  Hint Resolve context_equiv_ctl : lowering.

  Hint Resolve log_equiv_cons : lowering.

  Hint Rewrite @lower_unop_correct : lowering.
  Hint Rewrite @lower_binop_correct : lowering.
  Hint Rewrite @value_of_bits_of_value : lowering.

  Ltac destruct_res r :=
    destruct r as [((?, ?), ?) | ] eqn:?; cbn.

  Ltac lowering_correct_t_step :=
    match goal with
    | [  |- True ] => exact I
    | [ H: False |- _ ] => destruct H
    | _ => progress (subst; unfold opt_bind)
    | _ => cleanup_step
    | _ => progress autorewrite with lowering
    | _ => progress erewrite ?log_equiv_may_read, ?log_equiv_may_write,
          ?latest_write0_app, ?log_equiv_latest_write0 by eassumption
    | [  |- context[match ?res with _ => _ end] ] =>
      lazymatch res with
      | tinterp _ _ _ _ => destruct_res res
      | linterp _ _ _ _ => destruct_res res
      | Bits.single ?v => destruct v as [ [ | ] [] ]
      end
    | [ IH: (forall tGamma tL tl lGamma lL ll, let tres := tinterp tGamma tL tl ?ta in _),
        Ht: tinterp ?tGamma ?tL ?tl ?ta = _,
        Hl: linterp ?lGamma ?lL ?ll (lower_action ?ta) = _ |- _ ] =>
      specialize (IH tGamma tL tl lGamma lL ll);
      cbn in IH;
      (rewrite Ht in IH || setoid_rewrite Ht in IH);
      (rewrite Hl in IH || setoid_rewrite Hl in IH)
    | [ H: {| vhd := _; vtl := _ |} = {| vhd := _; vtl := _ |} |- _ ] =>
      inversion H; subst; clear H
    | [ IH: context_equiv _ _ -> _ |- _ ] =>
      specialize (IH ltac:(eauto with lowering))
    | [ IH: log_equiv _ _ -> _ |- _ ] =>
      specialize (IH ltac:(eauto))
    end.

  Ltac lowering_correct_t :=
    repeat lowering_correct_t_step; intuition eauto with lowering.

  Theorem action_lowering_correct:
    forall {sig tau} (ta: taction sig tau) tGamma tL tl lGamma lL ll,
      let tres := tinterp tGamma tL tl ta in
      let lres := linterp lGamma lL ll (lower_action ta) in
      context_equiv tGamma lGamma ->
      log_equiv tL lL ->
      log_equiv tl ll ->
      match tres, lres with
      | None, None => True
      | None, Some _ => False
      | Some _, None => False
      | Some (tl, tv, tGamma), Some (ll, lv, lGamma) =>
        lv = bits_of_value tv /\
        context_equiv tGamma lGamma /\
        log_equiv tl ll
      end.
  Proof.
    induction ta; simpl; intros.
    - lowering_correct_t.
    - lowering_correct_t.
    - lowering_correct_t.
    - lowering_correct_t.
    - lowering_correct_t.
    - lowering_correct_t.
    - lowering_correct_t.
    - lowering_correct_t.
      destruct Logs.may_read, port; lowering_correct_t.
      repeat destruct latest_write0; lowering_correct_t.
    - repeat lowering_correct_t_step.
      destruct Logs.may_write; lowering_correct_t.
    - lowering_correct_t.
    - lowering_correct_t.
    - lowering_correct_t.
    - lowering_correct_t.
  Qed.
End LoweringCorrectness.
