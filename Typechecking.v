Require Import SGA.Common SGA.Syntax SGA.Types.

Tactic Notation "teauto" := eauto with types.
Tactic Notation "teauto" integer(n) := eauto n with types.

Record fenv {Key Value: Type} :=
  { fn :> Key -> Value -> Prop;
    uniq: forall k v v', fn k v -> fn k v' -> v = v' }.

Arguments fenv: clear implicits.
Hint Resolve @uniq : types.

Definition fenv_add {Key Value: Type} (env: fenv Key Value) (k: Key) (v: Value) : fenv Key Value.
  refine {| fn := (fun k' v' => (k = k' /\ v = v') \/ (k <> k' /\ env.(fn) k' v')) |};
    abstract (destruct env; intuition (subst; teauto)).
Defined.

Definition fenv_le {Key Value: Type} (cmp : Value -> Value -> Prop) (Gamma Gamma': fenv Key Value) :=
  forall k v, Gamma k v -> exists v', Gamma' k v' /\ cmp v v'.

Lemma fenv_le_refl {Key Value: Type}:
  forall (cmp: _ -> _ -> Prop) (Gamma : fenv Key Value),
    (forall x, cmp x x) ->
    fenv_le cmp Gamma Gamma.
Proof.
  firstorder.
Qed.

Hint Resolve fenv_le_refl : types.

Lemma fenv_add_increasing {Key Value: Type}:
  forall (cmp: _ -> _ -> Prop) (Gamma1 : fenv Key Value) (var : Key) (tau tau' : Value) (Gamma2 : fenv Key Value),
    cmp tau tau' ->
    fenv_le cmp Gamma1 Gamma2 ->
    fenv_le cmp (fenv_add Gamma1 var tau) (fenv_add Gamma2 var tau').
Proof.
  unfold fenv_le, fenv_add; simpl; firstorder (subst; teauto).
Qed.

Hint Resolve fenv_add_increasing : types.

Section TC.
  Notation tenv A := (fenv A type).

  Context {TVar TFn: Type}.
  Context (V: fenv nat nat).
  Context (Sigma: fenv TFn ExternalSignature).

  Notation syntax := (syntax TVar TFn).
  Notation fenv_le := (fenv_le type_le).

  Inductive HasType : forall (Gamma: tenv TVar) (s: syntax) (tau: type), Prop :=
  | HasTypePromote:
      forall (Gamma: tenv TVar) (s: syntax)
        (tau: type) (tau': type),
        type_le tau tau' ->
        HasType Gamma s tau' ->
        HasType Gamma s tau
  | HasTypeBind:
      forall (Gamma: tenv TVar)
        (var: TVar) (expr: syntax) (body: syntax)
        (tau tau': type),
        HasType Gamma expr tau' ->
        HasType (fenv_add Gamma var tau') body tau ->
        HasType Gamma (Bind var expr body) tau
  | HasTypeVar:
      forall (Gamma: tenv TVar)
        (var: TVar)
        (tau: type),
        Gamma var tau ->
        HasType Gamma (Var var) tau
  | HasTypeSkip:
      forall (Gamma: tenv TVar),
        HasType Gamma Skip unit_t
  | HasTypeConst:
      forall (Gamma: tenv TVar)
        (cst: bits),
        HasType Gamma (Const cst) (bit_t (length cst))
  | HasTypeIf:
      forall (Gamma: tenv TVar)
        (cond: syntax) (tbranch: syntax) (fbranch: syntax)
        (tau: type),
        HasType Gamma cond (bit_t 1) ->
        HasType Gamma tbranch tau ->
        HasType Gamma fbranch tau ->
        HasType Gamma (If cond tbranch fbranch) tau
  | HasTypeFail:
      forall (Gamma: tenv TVar)
        (tau: type),
        HasType Gamma Fail tau
  | HasTypeRead:
      forall (Gamma: tenv TVar)
        (level: Level) (idx: nat)
        (size: nat) (n: nat),
        V idx size ->
        HasType Gamma (Read level idx) (bit_t size)
  | HasTypeWrite:
      forall (Gamma: tenv TVar)
        (level: Level) (idx: nat) (value: syntax)
        (size: nat) (n: nat),
        V idx size ->
        HasType Gamma value (bit_t size) ->
        HasType Gamma (Write level idx value) unit_t
  | HasTypeCall:
      forall (Gamma: tenv TVar)
        (idx: TFn) (args: list syntax)
        (argSizes: list nat) (retType: type),
        Sigma idx (FunSig argSizes retType) ->
        List.length args = List.length argSizes ->
        (forall (n: nat) (s: syntax) (argSize: nat),
            List.nth_error args n = Some s ->
            List.nth_error argSizes n = Some argSize ->
            HasType Gamma s (bit_t argSize)) ->
        HasType Gamma (Call idx args) retType.

  Hint Constructors HasType : types.

  Lemma HasType_morphism:
    forall (Gamma1: tenv TVar) s tau,
      HasType Gamma1 s tau ->
      forall (Gamma2: tenv TVar),
        fenv_le Gamma1 Gamma2 ->
        HasType Gamma2 s tau.
  Proof.
    induction 1; intros Gamma2 le; teauto 6.
    specialize (le _ _ H).
    firstorder teauto.
  Qed.

  Hint Resolve HasType_morphism : types.
  (* Note: no MaxType_morphism, since changing the environment changes the MaxType of the refs *)

  Inductive MaxType : forall (Gamma: tenv TVar) (s: syntax) (tau: type), Prop :=
  | MaxTypeBind:
      forall (Gamma: tenv TVar)
        (var: TVar) (expr: syntax) (body: syntax)
        (tau tau': type),
        MaxType Gamma expr tau' ->
        MaxType (fenv_add Gamma var tau') body tau ->
        MaxType Gamma (Bind var expr body) tau
  | MaxTypeVar:
      forall (Gamma: tenv TVar)
        (var: TVar)
        (tau: type),
        Gamma var tau ->
        MaxType Gamma (Var var) tau
  | MaxTypeSkip:
      forall (Gamma: tenv TVar),
        MaxType Gamma Skip unit_t
  | MaxTypeConst:
      forall (Gamma: tenv TVar)
        (cst: bits),
        MaxType Gamma (Const cst) (bit_t (length cst))
  | MaxTypeIfT:
      forall (Gamma: tenv TVar)
        (cond: syntax) (tbranch: syntax) (fbranch: syntax)
        (tauf taut: type),
        HasType Gamma cond (bit_t 1) ->
        MaxType Gamma tbranch tauf ->
        MaxType Gamma fbranch taut ->
        type_le taut tauf ->
        MaxType Gamma (If cond tbranch fbranch) taut
  | MaxTypeIfF:
      forall (Gamma: tenv TVar)
        (cond: syntax) (tbranch: syntax) (fbranch: syntax)
        (tauf taut: type),
        HasType Gamma cond (bit_t 1) ->
        MaxType Gamma tbranch tauf ->
        MaxType Gamma fbranch taut ->
        type_le tauf taut ->
        MaxType Gamma (If cond tbranch fbranch) tauf
  | MaxTypeFail:
      forall (Gamma: tenv TVar),
        MaxType Gamma Fail any_t
  | MaxTypeRead:
      forall (Gamma: tenv TVar)
        (level: Level) (idx: nat)
        (size: nat) (n: nat),
        V idx size ->
        MaxType Gamma (Read level idx) (bit_t size)
  | MaxTypeWrite:
      forall (Gamma: tenv TVar)
        (level: Level) (idx: nat) (value: syntax)
        (size: nat) (n: nat),
        V idx size ->
        HasType Gamma value (bit_t size) ->
        MaxType Gamma (Write level idx value) unit_t
  | MaxTypeCall:
      forall (Gamma: tenv TVar)
        (idx: TFn) (args: list syntax)
        (argSizes: list nat) (retType: type),
        Sigma idx (FunSig argSizes retType) ->
        List.length args = List.length argSizes ->
        (forall (n: nat) (s: syntax) (argSize: nat),
            List.nth_error args n = Some s ->
            List.nth_error argSizes n = Some argSize ->
            HasType Gamma s (bit_t argSize)) ->
        MaxType Gamma (Call idx args) retType.
  (* FIXME use single HasType premise in last three rules? *)

  Hint Constructors MaxType : types.

  Theorem maxtypes_unicity :
    forall Gamma s tau,
      MaxType Gamma s tau ->
      forall tau',
        MaxType Gamma s tau' ->
        tau = tau'.
  Proof.
    induction 1; intros * HasType';
      inversion HasType'; subst.
    1-12: solve [firstorder (subst; firstorder teauto)].
  Qed.

  Hint Resolve maxtypes_unicity : types.

  Lemma MaxType_HasType : forall Gamma s tau, MaxType Gamma s tau -> HasType Gamma s tau.
    induction 1; teauto.
  Qed.

  Notation "Gamma [ k ↦ v ]" :=
    (fenv_add Gamma k v) (at level 7, left associativity, format "Gamma [ k  ↦  v ]").
  Notation "Gamma ⊢ s :: tau" :=
    (HasType Gamma s tau) (at level 8, no associativity).
  Notation "Gamma ⊩ s :: tau" :=
    (MaxType Gamma s tau) (at level 8, no associativity).

  Notation "tau ⩽ tau'" :=
    (type_le tau tau') (at level 10, no associativity).

  Lemma type_le_inv :
    forall tau tau',
      tau ⩽ tau' ->
      tau' = any_t \/ tau' = tau.
  Proof.
    inversion 1; simpl; teauto.
  Qed.

  Lemma type_le_upper_bounds_comparable :
    forall tau1 tau2 tau1' tau2',
      tau1 ⩽ tau2 ->
      tau1 ⩽ tau1' ->
      tau2 ⩽ tau2' ->
      (tau1' ⩽ tau2' \/ tau2' ⩽ tau1').
  Proof.
    intros * le12 le11' le22';
      inversion le12; inversion le11'; inversion le22'; subst;
        discriminate || teauto.
  Qed.

  Ltac t :=
    repeat match goal with
           | [ H: fn ?Gamma ?k ?v, Hle: fenv_le ?Gamma _ |- _ ] =>
             pose_once Hle k v H
           | [ H: exists _, _ |- _ ] => destruct H
           | [ H: _ /\ _ |- _ ] => destruct H
           end.

  (* The other copies of MaxType_increasing aren't very interesting, since they don't show existence (and existence implies their results, because of unicity) *)
  Lemma MaxType_increasing'' : forall s Gamma tau,
      MaxType Gamma s tau ->
      forall (Gamma': tenv TVar),
        fenv_le Gamma Gamma' ->
        exists tau',
          MaxType Gamma' s tau' /\
          type_le tau tau'.
  Proof.
    induction 1; intros * le; t; teauto 7.

    - specialize (IHMaxType1 _ le).
      t.
      assert (fenv_le Gamma[var ↦ tau'] Gamma'[var ↦ x]) as Hdiff.
      { apply fenv_add_increasing; eassumption. }
      specialize (IHMaxType2 _ Hdiff).
      t.
      teauto.

    - specialize (IHMaxType1 _ le).
      t.
      specialize (IHMaxType2 _ le).
      t.

      destruct (type_le_upper_bounds_comparable
                  taut tauf _ _
                  ltac:(eassumption)
                  ltac:(eassumption)
                  ltac:(eassumption)).
      teauto.
      teauto 6.

    - specialize (IHMaxType1 _ le).
      t.
      specialize (IHMaxType2 _ le).
      t.

      destruct (type_le_upper_bounds_comparable
                  tauf taut _ _
                  ltac:(eassumption)
                  ltac:(eassumption)
                  ltac:(eassumption)).
      teauto.
      teauto 6.
  Qed.

  Lemma HasType_MaxType : forall Gamma s tau,
      HasType Gamma s tau ->
      exists tau', MaxType Gamma s tau' /\ tau ⩽ tau'.
  Proof.
    induction 1; try solve [teauto || firstorder teauto].
    - t.

      pose proof (MaxType_increasing''
                    _ _ _ H1 Gamma[var ↦ x0]
                    ltac:(teauto)).
      t.
      teauto.
    - t.

      destruct (type_le_upper_bounds_comparable
                  tau tau x x0
                  ltac:(teauto)
                  ltac:(eassumption)
                  ltac:(eassumption)).
      teauto.
      teauto.
  Qed.

  Lemma type_le_inv_not_any_t :
    forall tau tau',
      tau' ⩽ tau ->
      tau <> any_t ->
      tau' = tau.
  Proof.
    inversion 1; congruence.
  Qed.

  Hint Resolve type_le_inv_not_any_t : types.
  Hint Resolve MaxType_HasType : types.

  Theorem types_unicity :
    forall Gamma s tau,
      HasType Gamma s tau ->
      HasType Gamma s any_t \/
      forall tau', HasType Gamma s tau' -> tau = tau'.
  Proof.
    intros Gamma s tau H.
    pose proof (HasType_MaxType _ _ _ H).
    t.
    destruct (type_eq_dec x any_t); subst.
    - teauto.
    - right.
      intros tau' H'.
      pose proof (HasType_MaxType _ _ _ H').
      t.
      assert (x = x0) by teauto; subst.

      transitivity x0.
      teauto.
      teauto.
  Qed.

  Print Assumptions types_unicity.
End TC.
