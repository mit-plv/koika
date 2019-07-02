Require Import List.
Require Import SGA.Common SGA.Syntax.

(** Environments **)
Record fenv {Key Value} :=
  { fn :> Key -> Value -> Prop;
    uniq: forall k v v', fn k v -> fn k v' -> v = v' }.

Arguments fenv: clear implicits.

Definition fenv_lookup {Key Value} (env: fenv Key Value) k v := env.(fn) k v.

Definition fenv_add {Key Value} (env: fenv Key Value) (k: Key) (v: Value) : fenv Key Value.
  refine {| fn := (fun k' v' => (k = k' /\ v = v') \/ (k <> k' /\ env.(fn) k' v')) |};
    abstract (destruct env; intuition (subst; eauto)).
Defined.

(* FIXME: remove *)
Definition fenv_incl_domains {Key} {Value} (Gamma Gamma': fenv Key Value) :=
  forall k v, Gamma k v -> exists v', Gamma' k v'.

Lemma fenv_incl_domains_add {Key Value}:
  forall (Gamma Gamma': fenv Key Value) k v v',
    fenv_incl_domains Gamma Gamma' ->
    fenv_incl_domains (fenv_add Gamma k v) (fenv_add Gamma' k v').
Proof.
  unfold fenv_incl_domains, fenv_add; simpl; firstorder (subst; eauto).
Qed.

Definition fenv_le {Key Value} (cmp : Value -> Value -> Prop) (Gamma Gamma': fenv Key Value) :=
  forall k v, Gamma k v -> exists v', Gamma' k v' /\ cmp v v'.

Lemma fenv_le_refl {Key Value} :
  forall (cmp: _ -> _ -> Prop) (Gamma : fenv Key Value),
    (forall x, cmp x x) ->
    fenv_le cmp Gamma Gamma.
Proof.
  firstorder.
Qed.

Hint Resolve fenv_le_refl.

Lemma fenv_add_increasing {Var Value}:
  forall (cmp: _ -> _ -> Prop) (Gamma1 : fenv Var Value) (var : Var) (tau tau' : Value) (Gamma2 : fenv Var Value),
    cmp tau tau' ->
    fenv_le cmp Gamma1 Gamma2 ->
    fenv_le cmp (fenv_add Gamma1 var tau) (fenv_add Gamma2 var tau').
Proof.
  unfold fenv_le, fenv_add; simpl; firstorder (subst; eauto).
Qed.

Record FunSig T := SigFn { argTypes: list T; retType: T }.
Arguments SigFn {_}.

Hint Resolve @uniq : core.

Lemma SigFunction_inj2 {T} :
  forall (argTypes argTypes': list T) (retType retType': T),
    SigFn argTypes retType =
    SigFn argTypes' retType' ->
    retType = retType'.
Proof. now inversion 1. Qed.

Hint Extern 10 => eapply @SigFunction_inj2.

Inductive Posed {P: Prop}: P -> Prop :=
| AlreadyPosed : forall p: P, Posed p.

Tactic Notation "pose_once" uconstr(thm) :=
  (progress match goal with
            | [ H: Posed ?thm' |- _ ] =>
              unify thm thm'
            | _ => pose proof thm;
                  pose proof (AlreadyPosed thm)
            end).

Inductive type :=
| unit_t
| bit_t (n: nat)
| any_t.

Scheme Equality for type.

Inductive type_le : type -> type -> Prop :=
| TypeLeRefl : forall tau tau', tau' = tau -> type_le tau tau'
| TypeLeAny : forall tau tau', tau' = any_t -> type_le tau tau'.

Hint Constructors type_le.

Lemma type_le_trans:
  forall tau1 tau2 tau3,
    type_le tau1 tau2 ->
    type_le tau2 tau3 ->
    type_le tau1 tau3.
Proof.
  intros * le12 le23. destruct le12, le23; subst; eauto.
Qed.

Hint Resolve type_le_trans.

Lemma type_le_antisym:
  forall tau1 tau2,
    type_le tau1 tau2 ->
    type_le tau2 tau1 ->
    tau1 = tau2.
Proof.
  intros * le12 le23. destruct le12, le23; subst; eauto.
Qed.

Hint Resolve type_le_antisym.

Lemma type_ge_any_t_eq_any_t :
  forall tau,
    type_le any_t tau ->
    tau = any_t.
Proof.
  inversion 1; eauto.
Qed.

Hint Resolve type_ge_any_t_eq_any_t.

(* Inductive unifiable : type -> type -> Prop := *)
(* | urefl : forall tau, unifiable tau tau *)
(* | uany_tl : forall tau, unifiable any_t tau *)
(* | uany_tr : forall tau, unifiable tau any_t. *)

Notation tenv A := (fenv A type).

Hint Resolve fenv_incl_domains_add.

Hint Resolve fenv_add_increasing.

Section TC.
  Context {TVar TFn: Type}.
  Context (Sigma__reg: fenv nat type).
  Context (Sigma__fn: fenv TFn (FunSig type)).

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
        (bits: list bool) (cst: nat),
        HasType Gamma (Const bits) (bit_t (length bits))
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
        (tau: type) (n: nat),
        Sigma__reg idx tau ->
        HasType Gamma (Read level idx) tau
  | HasTypeWrite:
      forall (Gamma: tenv TVar)
        (level: Level) (idx: nat) (value: syntax)
        (tau: type) (n: nat),
        Sigma__reg idx tau ->
        HasType Gamma value tau ->
        HasType Gamma (Write level idx value) unit_t
  | HasTypeCall:
      forall (Gamma: tenv TVar)
        (idx: TFn) (args: list syntax)
        (argTypes: list type) (retType: type),
        Sigma__fn idx (SigFn argTypes retType) ->
        List.length args = List.length argTypes ->
        (forall (n: nat) (s: syntax) (tau: type),
            List.nth_error args n = Some s ->
            List.nth_error argTypes n = Some tau ->
            HasType Gamma s tau) ->
        HasType Gamma (Call idx args) retType.

  Hint Constructors HasType.

  Lemma HasType_morphism:
    forall (Gamma1: tenv TVar) s tau,
      HasType Gamma1 s tau ->
      forall (Gamma2: tenv TVar),
        fenv_le Gamma1 Gamma2 ->
        HasType Gamma2 s tau.
  Proof.
    induction 1; intros Gamma2 le; eauto 6.
    specialize (le _ _ H).
    firstorder eauto.
  Qed.

  Hint Resolve HasType_morphism.
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
        (bits: list bool) (cst: nat),
        MaxType Gamma (Const bits) (bit_t (length bits))
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
        (tau: type) (n: nat),
        Sigma__reg idx tau ->
        MaxType Gamma (Read level idx) tau
  | MaxTypeWrite:
      forall (Gamma: tenv TVar)
        (level: Level) (idx: nat) (value: syntax)
        (tau: type) (n: nat),
        Sigma__reg idx tau ->
        HasType Gamma value tau ->
        MaxType Gamma (Write level idx value) unit_t
  | MaxTypeCall:
      forall (Gamma: tenv TVar)
        (idx: TFn) (args: list syntax)
        (argTypes: list type) (retType: type),
        Sigma__fn idx (SigFn argTypes retType) ->
        List.length args = List.length argTypes ->
        (forall (n: nat) (s: syntax) (tau: type),
            List.nth_error args n = Some s ->
            List.nth_error argTypes n = Some tau ->
            HasType Gamma s tau) ->
        MaxType Gamma (Call idx args) retType.
  (* FIXME use single HasType premise in last three rules? *)

  Hint Constructors MaxType.

  Theorem maxtypes_unicity :
    forall Gamma s tau,
      MaxType Gamma s tau ->
      forall tau',
        MaxType Gamma s tau' ->
        tau = tau'.
  Proof.
    induction 1; intros * HasType';
      inversion HasType'; subst.
    1-12: solve [firstorder (subst; firstorder eauto)].
  Qed.

  Hint Resolve maxtypes_unicity.

  Lemma MaxType_HasType : forall Gamma s tau, MaxType Gamma s tau -> HasType Gamma s tau.
    induction 1; eauto.
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
    inversion 1; simpl; eauto.
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
        discriminate || eauto.
  Qed.

  Ltac t :=
    repeat match goal with
           | [ H: fn ?Gamma _ _, Hle: fenv_le ?Gamma _ |- _ ] =>
             pose_once (Hle _ _ H)
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
    induction 1; intros * le; t; eauto 7.

    - specialize (IHMaxType1 _ le).
      t.
      assert (fenv_le Gamma[var ↦ tau'] Gamma'[var ↦ x]) as Hdiff.
      { apply fenv_add_increasing; eassumption. }
      specialize (IHMaxType2 _ Hdiff).
      t.
      eauto.

    - specialize (IHMaxType1 _ le).
      t.
      specialize (IHMaxType2 _ le).
      t.

      destruct (type_le_upper_bounds_comparable
                  taut tauf _ _
                  ltac:(eassumption)
                  ltac:(eassumption)
                  ltac:(eassumption)).
      eauto.
      eauto 6.

    - specialize (IHMaxType1 _ le).
      t.
      specialize (IHMaxType2 _ le).
      t.

      destruct (type_le_upper_bounds_comparable
                  tauf taut _ _
                  ltac:(eassumption)
                  ltac:(eassumption)
                  ltac:(eassumption)).
      eauto.
      eauto 6.
  Qed.

  Lemma HasType_MaxType : forall Gamma s tau,
      HasType Gamma s tau ->
      exists tau', MaxType Gamma s tau' /\ tau ⩽ tau'.
  Proof.
    induction 1; try solve [eauto || firstorder eauto].
    - t.

      pose proof (MaxType_increasing''
                    _ _ _ H1 Gamma[var ↦ x0]
                    ltac:(eauto)).
      t.
      eauto.
    - t.

      destruct (type_le_upper_bounds_comparable
                  tau tau x x0
                  ltac:(eauto)
                  ltac:(eassumption)
                  ltac:(eassumption)).
      eauto.
      eauto.
  Qed.

  Lemma type_le_inv_not_any_t :
    forall tau tau',
      tau' ⩽ tau ->
      tau <> any_t ->
      tau' = tau.
  Proof.
    inversion 1; congruence.
  Qed.

  Hint Resolve type_le_inv_not_any_t.

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
    - eauto using MaxType_HasType.
    - right.
      intros tau' H'.
      pose proof (HasType_MaxType _ _ _ H').
      t.
      assert (x = x0) by eauto; subst.

      transitivity x0.
      eauto.
      eauto.
  Qed.

  Print Assumptions types_unicity.
End TC.
