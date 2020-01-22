(*! Circuits | Proof of correctness for the lowering phase !*)
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Ring Coq.setoid_ring.Ring.
Require Import Koika.Common Koika.Environments Koika.Syntax
        Koika.SemanticProperties Koika.PrimitiveProperties Koika.SyntaxMacros Koika.Lowering.
Require Koika.TypedSemantics Koika.LoweredSemantics.
Import EqNotations.

Section LoweringCorrectness.
  Context {pos_t var_t fn_name_t rule_name_t reg_t ext_fn_t: Type}.

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

  Notation taction := (TypedSyntax.action pos_t var_t fn_name_t R Sigma).
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

  Definition lower_context  {sig}
             (tGamma: tcontext sig) :=
    cmap (V := fun k_tau => type_denote (snd k_tau))
         (V' := Bits.bits)
         (fun k_tau => type_sz (@snd var_t type k_tau))
         (fun _ v => bits_of_value v)
         tGamma.
  Arguments lower_context : simpl never.

  Definition context_equiv {sig}
             (tGamma: tcontext sig)
             (lGamma: lcontext (lsig_of_tsig sig)) :=
    lGamma = lower_context tGamma.

  Lemma context_equiv_cassoc {sig: tsig var_t} :
    forall (tGamma: tcontext sig) {k tau} (m: member (k, tau) sig),
        cassoc (lower_member m) (lower_context tGamma) =
        bits_of_value (cassoc m tGamma).
  Proof.
    intros; rewrite <- (cmap_cassoc _ (fun _ v => bits_of_value v) _ m); reflexivity.
  Qed.

  Lemma context_equiv_creplace:
    forall {sig: tsig var_t} {k: var_t} {tau: type}
      (m: member (k, tau) sig) (v: tau)
      (tGamma: tcontext sig),
      context_equiv
        (creplace m v tGamma)
        (creplace (lower_member m) (bits_of_value v) (lower_context tGamma)).
  Proof.
    unfold context_equiv, lower_member, lower_context; intros.
    rewrite cmap_creplace; reflexivity.
  Qed.

  Lemma context_equiv_CtxCons:
    forall (sig: tsig var_t) (tau: type) (k: var_t) (v: tau) (tGamma: tcontext sig),
      context_equiv (CtxCons (k, tau) v tGamma)
                    (CtxCons (type_sz tau) (bits_of_value v) (lower_context tGamma)).
  Proof. reflexivity. Qed.

  Lemma context_equiv_ctl:
    forall (sig: tsig var_t) (tau: type) (k: var_t)
      (tGamma: tcontext ((k, tau) :: sig)),
      context_equiv (ctl tGamma) (ctl (lower_context tGamma)).
  Proof.
    unfold context_equiv, lower_context; intros; rewrite cmap_ctl; reflexivity.
  Qed.

  Definition lower_log (tL: tlog) :=
    log_map_values (fun idx => bits_of_value) tL.
  Arguments lower_log : simpl never.

  Definition log_equiv (tL: tlog) (lL: llog) : Prop :=
    lL = lower_log tL.

  Lemma log_equiv_empty:
    log_equiv log_empty log_empty.
  Proof.
    unfold log_equiv; symmetry; apply log_map_values_empty.
  Qed.

  Lemma log_equiv_cons:
    forall (tL: tlog) idx tle,
      log_equiv (log_cons idx tle tL)
                (log_cons idx (LogEntry_map bits_of_value tle) (lower_log tL)).
  Proof.
    intros; red; unfold lower_log; rewrite log_map_values_cons; reflexivity.
  Qed.

  Lemma log_equiv_app:
    forall (tL tl: tlog),
      log_equiv (log_app tL tl)
                (log_app (lower_log tL) (lower_log tl)).
  Proof.
    unfold log_equiv, lower_log; intros.
    rewrite <- log_map_values_log_app; reflexivity.
  Qed.

  Lemma log_equiv_may_read:
    forall (tL: tlog) (port: Port) (idx: reg_t),
      Logs.may_read tL port idx =
      Logs.may_read (_R := CR) (lower_log tL) port idx.
  Proof. intros; symmetry; apply may_read_log_map_values. Qed.

  Lemma log_equiv_may_write:
    forall (tL tl: tlog) (port: Port) (idx: reg_t),
      Logs.may_write tL tl port idx =
      Logs.may_write (_R := CR) (lower_log tL) (lower_log tl) port idx.
  Proof. intros; symmetry; apply may_write_log_map_values. Qed.

  Lemma log_equiv_latest_write0:
    forall (tl: tlog) idx,
      latest_write0 (lower_log tl) idx =
      match latest_write0 tl idx with
      | Some v => Some (bits_of_value v)
      | None => None
      end.
  Proof.
    intros; unfold lower_log; rewrite latest_write0_log_map_values; reflexivity.
  Qed.

  Definition lower_result {sig tau} (r: option (tlog * type_denote tau * tcontext sig))
    : option (llog * bits (type_sz tau) * lcontext (lsig_of_tsig sig)) :=
    match r with
    | None => None
    | Some (tl, tv, tGamma) =>
      Some (lower_log tl, bits_of_value tv, lower_context tGamma)
    end.

  Definition lower_results {sig argspec} (r: option (tlog * tcontext argspec * tcontext sig))
    : option (llog * lcontext _ * lcontext (lsig_of_tsig sig)) :=
    match r with
    | None => None
    | Some (tl, tvs, tGamma) =>
      Some (lower_log tl,
            cmap (fun (k_tau: var_t * type) => type_sz (snd k_tau))
                 (fun k v => bits_of_value v)
                 tvs,
            lower_context tGamma)
    end.

  Definition lacontext (sig arg_sigs: lsig) :=
    context (fun sz => laction sig sz) arg_sigs.

  Fixpoint linterp_args
             {sig: lsig}
             (Gamma: lcontext sig)
             (sched_log: llog)
             (action_log: llog)
             {arg_sigs: lsig}
             (args: context (fun sz => var_t * laction sig sz)%type arg_sigs)
    : option (llog * lcontext arg_sigs * (lcontext sig)) :=
    match args with
    | CtxEmpty => Some (action_log, CtxEmpty, Gamma)
    | @CtxCons _ _ arg_sigs k_tau (k, arg) args =>
      let/opt3 action_log, ctx, Gamma := linterp_args Gamma sched_log action_log args in
      let/opt3 action_log, v, Gamma := linterp Gamma sched_log action_log arg in
      Some (action_log, CtxCons _ v ctx, Gamma)
    end.

  Lemma interp_infixed':
    forall {sg: lsig} {sz: nat} (a: laction sg sz) {sig sig'} (Heq: sg = sig ++ sig')
      {infix: lsig} (gamma: lcontext infix) (Gamma : lcontext sg)
      (L l: llog),
      linterp (infix_context gamma (rew Heq in Gamma)) L l
              (infix_action infix (rew [fun sg => laction sg sz] Heq in a)) =
      match linterp Gamma L l a with
      | Some (l, v, Gamma) => Some (l, v, infix_context gamma (rew Heq in Gamma))
      | None => None
      end.
  Proof.
    Arguments infix_context : simpl never.
    induction a;
      repeat match goal with
             | _ => reflexivity
             | _ => progress intros
             | _ => progress subst
             | _ => progress cbn
             | _ => progress change (CtxCons ?sz ?v (infix_context ?gamma ?Gamma)) with
                   (infix_context (sig := sz :: _) gamma (CtxCons sz v Gamma))
             | [ H: forall _ _ (Heq: _ = _), _ |- _ ] =>
               change (?x :: ?a ++ ?b) with ((x :: a) ++ b) in H;
               specialize (H _ _ eq_refl); cbn in H
             | [ H: context[_ = _] |- _ ] => rewrite H
             | [ |- context[if ?x then _ else _] ] => destruct x
             | _ => destruct linterp as [((?, ?), ?) | ]; [ | reflexivity ]
             | _ => rewrite ?cassoc_minfix, ?creplace_minfix
             end.
  Qed.

  Lemma interp_infixed:
    forall {sig sig': lsig} {sz: nat} (a: laction (sig ++ sig') sz)
      {infix: lsig} (gamma: lcontext infix) (Gamma : lcontext (sig ++ sig'))
      (L l: llog),
      linterp (infix_context gamma Gamma) L l (infix_action infix a) =
      match linterp Gamma L l a with
      | Some (l, v, Gamma) => Some (l, v, infix_context gamma Gamma)
      | None => None
      end.
  Proof. intros; apply (interp_infixed' a eq_refl). Qed.

  Lemma interp_prefixed:
    forall {sig: lsig} {sz: nat} (a: laction sig sz)
      {prefix: lsig} (gamma: lcontext prefix) (Gamma : lcontext sig)
      (L l: llog),
      linterp (capp gamma Gamma) L l (prefix_action prefix a) =
      match linterp Gamma L l a with
      | Some (l, v, Gamma) => Some (l, v, capp gamma Gamma)
      | None => None
      end.
  Proof. intros; apply (@interp_infixed []). Qed.

  Lemma linterp_cast:
    forall {sg: lsig} {sz: nat} f (a: laction (f sg) sz) {sg'} (Heq: sg = sg')
      (Gamma : lcontext (f sg)) (L l: llog),
      linterp (rew [fun sg => lcontext (f sg)] Heq in Gamma) L l
              (rew [fun sg => laction (f sg) sz] Heq in a) =
      rew [fun sg => option (llog * bits sz * lcontext (f sg))] Heq in
        (linterp Gamma L l a).
  Proof. destruct Heq; cbn; reflexivity. Qed.

  Lemma interp_suffixed:
    forall {sig: lsig} {sz: nat} (a: laction sig sz)
      {suffix: lsig} (gamma: lcontext suffix) (Gamma : lcontext sig)
      (L l: llog),
      linterp (capp Gamma gamma) L l (suffix_action suffix a) =
      match linterp Gamma L l a with
      | Some (l, v, Gamma) => Some (l, v, capp Gamma gamma)
      | None => None
      end.
  Proof. unfold suffix_action; intros.
     rewrite capp_as_infix.
     rewrite linterp_cast.
     unfold eq_rect_r; rewrite interp_infixed'.
     destruct linterp as [((?, ?), ?) | ]; cbn.
     - rewrite capp_as_infix.
       destruct (capp_nil_r suffix); cbn.
       reflexivity.
     - destruct capp_nil_r; reflexivity.
  Qed.

  Theorem InternalCall'_linterp_args :
    forall {sig sz argspec} (args: context (fun sz => var_t * laction sig sz)%type argspec)
      Gamma L l (body: laction (argspec ++ sig) sz),
      linterp Gamma L l (InternalCall' args body) =
      (let/opt3 l', results, Gamma' := linterp_args Gamma L l args in
       let/opt3 l'', v, Gamma'' := linterp (capp results Gamma') L l' body in
       Some (l'', v, snd (csplit Gamma''))).
  Proof.
    induction args as [ | sig' sz' (var, arg) tl IH ]; cbn; intros.
    - destruct linterp as [((?, ?), ?) | ]; reflexivity.
    - rewrite IH; cbn.
      destruct linterp_args as [((?, ?), ?) | ]; cbn; try reflexivity.
      rewrite interp_prefixed.
      repeat (destruct linterp as [((?, ?), ?) | ]; cbn; try reflexivity).
  Qed.

  Section Args.
    Context (IH: forall sig tau (v: taction sig tau) (Gamma: tcontext sig) tL tl,
                linterp (lower_context Gamma) (lower_log tL) (lower_log tl) (lower_action v) =
                lower_result (tinterp Gamma tL tl v)).

    Lemma linterp_args_correct:
      forall {sig argspec} (args : context (fun k_tau : var_t * type => taction sig (snd k_tau)) argspec)
        (tGamma: tcontext sig) tL tl,
        linterp_args (lower_context tGamma) (lower_log tL) (lower_log tl) (lower_args args) =
        lower_results (interp_args r sigma tGamma tL tl args).
    Proof.
      induction args; cbn; intros.
      - reflexivity.
      - rewrite IHargs by eauto.
        destruct (interp_args _ _ _ _ _ _) as [((?, ?), ?) | ]; cbn; try reflexivity.
        rewrite IH; destruct tinterp as [((?, ?), ?) | ]; reflexivity.
    Defined.

    Lemma InternalCall_correct:
      forall {sig argspec} (args : context (fun k_tau : var_t * type => taction sig (snd k_tau)) argspec)
        {tau} (ta: taction argspec tau) (tGamma : tcontext sig) tL tl,
        linterp (lower_context tGamma) (lower_log tL) (lower_log tl)
                (InternalCall (lower_args args) (lower_action ta)) =
        lower_result
          (let/opt3 action_log, results, Gamma := interp_args r sigma tGamma tL tl args in
           let/opt3 action_log0, v, _ := tinterp results tL action_log ta in
           Some (action_log0, v, Gamma)).
    Proof.
      unfold InternalCall; intros.
      rewrite InternalCall'_linterp_args.
      rewrite linterp_args_correct by auto.
      destruct (interp_args r sigma tGamma tL tl args) as [((?, ?), ?) | ]; cbn; try reflexivity.
      rewrite interp_suffixed.
      rewrite IH.
      destruct tinterp as [((?, ?), ?) | ]; cbn.
      - rewrite csplit_capp; reflexivity.
      - reflexivity.
    Defined.
  End Args.

  Create HintDb lowering.

  Hint Rewrite @context_equiv_cassoc : lowering.
  Hint Rewrite @context_equiv_creplace : lowering.
  Hint Rewrite @context_equiv_CtxCons : lowering.
  Hint Rewrite @context_equiv_ctl : lowering.
  Hint Rewrite <- @log_equiv_cons : lowering.
  Hint Rewrite @lower_unop_correct : lowering.
  Hint Rewrite @lower_binop_correct : lowering.
  Hint Rewrite @value_of_bits_of_value : lowering.
  Hint Rewrite @lower_r_eqn : lowering.
  Hint Rewrite @lower_sigma_eqn : lowering.
  Hint Rewrite @log_equiv_may_read : lowering.
  Hint Rewrite @log_equiv_may_write : lowering.
  Hint Rewrite @log_equiv_latest_write0 : lowering.
  Hint Rewrite @latest_write0_app : lowering.
  Hint Rewrite @csplit_capp : lowering.
  Hint Rewrite @InternalCall_correct : lowering.

  Ltac destruct_res r :=
    destruct r as [((?, ?), ?) | ] eqn:?; cbn.

  Ltac lowering_correct_t_step :=
    match goal with
    | _ => cleanup_step
    | _ => progress (subst; unfold opt_bind)
    | _ => progress autorewrite with lowering
    | [ H: context[linterp _ _ _ _ = _] |-
        context[linterp (lower_context ?G) (lower_log ?L) (lower_log ?l) (lower_action ?ta)] ] =>
      setoid_rewrite (H _ _ ta G L l)
    | [  |- context[linterp (CtxCons _ _ _) _ _ _] ] => setoid_rewrite context_equiv_CtxCons
    | [  |- context[ctl (lower_context _)] ] => setoid_rewrite context_equiv_ctl
    | [  |- context[tinterp] ] => destruct tinterp as [((?, ?), ?) | ]
    | [  |- context[latest_write0] ] => destruct latest_write0
    | [  |- context[if ?x then _ else _] ] => destruct x
    | _ => eauto using InternalCall_correct
    end.

  Ltac lowering_correct_t :=
    repeat lowering_correct_t_step.

  Theorem action_lowering_correct:
    forall {sig tau} (ta: taction sig tau) tGamma tL tl,
      linterp (lower_context tGamma) (lower_log tL) (lower_log tl) (lower_action ta) =
      lower_result (tinterp tGamma tL tl ta).
  Proof.
    fix IHta 3; destruct ta; simpl; intros; cbn.

    - lowering_correct_t.
    - lowering_correct_t.
    - lowering_correct_t.
    - lowering_correct_t.
    - lowering_correct_t.
    - lowering_correct_t.
    - lowering_correct_t.
    - lowering_correct_t.
    - lowering_correct_t.
    - lowering_correct_t.
    - lowering_correct_t.
    - lowering_correct_t.
    - lowering_correct_t.
    - lowering_correct_t.
  Qed.

  Context (rules: rule_name_t -> TypedSyntax.rule pos_t var_t fn_name_t R Sigma).
  Notation lrules r := (lower_action (rules r)).

  Lemma scheduler_lowering_correct':
    forall s L,
      LoweredSemantics.interp_scheduler' lr lsigma (fun r => lrules r) (lower_log L) s =
      lower_log (TypedSemantics.interp_scheduler' r sigma rules L s).
  Proof.
    induction s; intros; cbn;
      unfold TypedSemantics.interp_rule, LoweredSemantics.interp_rule.
    - reflexivity.
    - rewrite log_equiv_empty.
      setoid_rewrite (action_lowering_correct (rules r0) CtxEmpty L log_empty).
      destruct tinterp as [((?, ?), ?) | ]; cbn;
        try rewrite log_equiv_app; eauto.
    - rewrite log_equiv_empty.
      setoid_rewrite (action_lowering_correct (rules r0) CtxEmpty L log_empty).
      destruct tinterp as [((?, ?), ?) | ]; cbn;
        try rewrite log_equiv_app; eauto.
    - eauto.
  Qed.

  Theorem scheduler_lowering_correct:
    forall s,
      LoweredSemantics.interp_scheduler lr lsigma (fun r => lrules r) s =
      lower_log (TypedSemantics.interp_scheduler r sigma rules s).
  Proof.
    unfold TypedSemantics.interp_scheduler; intros.
    rewrite <- scheduler_lowering_correct', <- log_equiv_empty; reflexivity.
  Qed.
End LoweringCorrectness.
