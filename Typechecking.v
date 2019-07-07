Require Import SGA.Common SGA.Syntax SGA.Environments SGA.Types.

Tactic Notation "teauto" := eauto with types.
Tactic Notation "teauto" integer(n) := eauto n with types.

Section TC.
  Notation tenv A := (fenv A type).

  Context {TVar TFn: Type}.
  Context (V: fenv nat nat).
  Context (Sigma: fenv TFn ExternalSignature).

  Notation rule := (rule TVar TFn).
  Notation fenv_le := (fenv_le type_le).

  Inductive HasType : forall (Gamma: tenv TVar) (s: rule) (tau: type), Prop :=
  | HasTypePromote:
      forall (Gamma: tenv TVar) (s: rule)
        (tau: type) (tau': type),
        type_le tau tau' ->
        HasType Gamma s tau' ->
        HasType Gamma s tau
  | HasTypeBind:
      forall (Gamma: tenv TVar)
        (var: TVar) (expr: rule) (body: rule)
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
        (cond: rule) (tbranch: rule) (fbranch: rule)
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
        (level: Level) (idx: nat) (value: rule)
        (size: nat) (n: nat),
        V idx size ->
        HasType Gamma value (bit_t size) ->
        HasType Gamma (Write level idx value) unit_t
  | HasTypeCall:
      forall (Gamma: tenv TVar)
        (idx: TFn) (args: list rule)
        (argSizes: list nat) (retType: type),
        Sigma idx (FunSig argSizes retType) ->
        List.length args = List.length argSizes ->
        forall2 (fun arg argSize => HasType Gamma arg (bit_t argSize)) args argSizes ->
        HasType Gamma (Call idx args) retType.

  Hint Constructors HasType : types.
  Hint Extern 1 => unfold forall2 in * : types.

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

  Inductive MaxType : forall (Gamma: tenv TVar) (s: rule) (tau: type), Prop :=
  | MaxTypeBind:
      forall (Gamma: tenv TVar)
        (var: TVar) (expr: rule) (body: rule)
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
  | MaxTypeIfF:
      forall (Gamma: tenv TVar)
        (cond: rule) (tbranch: rule) (fbranch: rule)
        (tauf taut: type),
        HasType Gamma cond (bit_t 1) ->
        MaxType Gamma tbranch taut ->
        MaxType Gamma fbranch tauf ->
        type_le tauf taut ->
        MaxType Gamma (If cond tbranch fbranch) tauf
  | MaxTypeIfT:
      forall (Gamma: tenv TVar)
        (cond: rule) (tbranch: rule) (fbranch: rule)
        (tauf taut: type),
        HasType Gamma cond (bit_t 1) ->
        MaxType Gamma tbranch taut ->
        MaxType Gamma fbranch tauf ->
        type_le taut tauf ->
        MaxType Gamma (If cond tbranch fbranch) taut
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
        (level: Level) (idx: nat) (value: rule)
        (size: nat) (n: nat),
        V idx size ->
        HasType Gamma value (bit_t size) ->
        MaxType Gamma (Write level idx value) unit_t
  | MaxTypeCall:
      forall (Gamma: tenv TVar)
        (idx: TFn) (args: list rule)
        (argSizes: list nat) (retType: type),
        Sigma idx (FunSig argSizes retType) ->
        List.length args = List.length argSizes ->
        forall2 (fun arg argSize => HasType Gamma arg (bit_t argSize)) args argSizes ->
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

  Lemma MaxType_HasType : forall Gamma s tau', MaxType Gamma s tau' -> forall tau, type_le tau tau' -> HasType Gamma s tau.
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

  Ltac t :=
    repeat match goal with
           | [ H: fn ?Gamma ?k ?v, Hle: fenv_le ?Gamma _ |- _ ] =>
             pose_once Hle k v H
           | [ H: exists _, _ |- _ ] => destruct H
           | [ H: _ /\ _ |- _ ] => destruct H
           end.

  Lemma MaxType_increasing'' : forall s Gamma tau,
      MaxType Gamma s tau ->
      forall (Gamma': tenv TVar),
        fenv_le Gamma Gamma' ->
        exists tau',
          MaxType Gamma' s tau' /\
          type_le tau tau'.
  Proof.
    induction 1; intros * le; t; teauto 6.

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
                  tauf taut _ _
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
                  taut tauf _ _
                  ltac:(eassumption)
                  ltac:(eassumption)
                  ltac:(eassumption)).
      teauto.
      teauto 6.
    - teauto 8.
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

  Notation scheduler := (scheduler TVar TFn).

  Inductive SchedulerHasTypes: forall (s: scheduler), Prop :=
  | SchedulerHasTypesDone : SchedulerHasTypes Done
  | SchedulerHasTypesTry :
      forall r tau s1 s2,
        HasType fenv_nil r tau ->
        SchedulerHasTypes s1 ->
        SchedulerHasTypes s2 ->
        SchedulerHasTypes (Try r s1 s2).
End TC.
