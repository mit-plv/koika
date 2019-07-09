Require Import List.
Require Import SGA.Common SGA.Syntax.

Inductive type :=
| unit_t
| bit_t (n: nat)
| any_t.

Scheme Equality for type.

Inductive type_le : type -> type -> Prop :=
| TypeLeRefl : forall tau tau', tau' = tau -> type_le tau tau'
| TypeLeAny : forall tau tau', tau' = any_t -> type_le tau tau'.

Hint Constructors type_le : types.

Ltac teauto := eauto with types.

Lemma type_le_trans:
  forall tau1 tau2 tau3,
    type_le tau1 tau2 ->
    type_le tau2 tau3 ->
    type_le tau1 tau3.
Proof.
  intros * le12 le23. destruct le12, le23; subst; teauto.
Qed.

Hint Resolve type_le_trans : types.

Lemma type_le_antisym:
  forall tau1 tau2,
    type_le tau1 tau2 ->
    type_le tau2 tau1 ->
    tau1 = tau2.
Proof.
  intros * le12 le23. destruct le12, le23; subst; teauto.
Qed.

Hint Resolve type_le_antisym : types.

Lemma type_ge_any_t_eq_any_t :
  forall tau,
    type_le any_t tau ->
    tau = any_t.
Proof.
  inversion 1; teauto.
Qed.

Hint Resolve type_ge_any_t_eq_any_t : types.

Lemma type_le_inv_not_any_t :
  forall tau tau',
    type_le tau' tau ->
    tau <> any_t ->
    tau' = tau.
Proof.
  inversion 1; congruence.
Qed.

Lemma type_le_inv :
  forall tau tau',
    type_le tau tau' ->
    tau' = any_t \/ tau' = tau.
Proof.
  inversion 1; simpl; teauto.
Qed.

Hint Resolve type_le_inv_not_any_t : types.

Lemma type_le_upper_bounds_comparable :
  forall tau1 tau2 tau1' tau2',
    type_le tau1 tau2 ->
    type_le tau1 tau1' ->
    type_le tau2 tau2' ->
    (type_le tau1' tau2' \/ type_le tau2' tau1').
Proof.
  intros * le12 le11' le22';
    inversion le12; inversion le11'; inversion le22'; subst;
      discriminate || teauto.
Qed.


Record ExternalSignature :=
  FunSig { argSizes: list nat;
           retSize: nat }.

Lemma ExternalSignature_inj2 :
  forall (argSizes argSizes': list nat) (retSize retSize': nat),
    FunSig argSizes retSize =
    FunSig argSizes' retSize' ->
    retSize = retSize'.
Proof. now inversion 1. Qed.

Hint Extern 10 => eapply @ExternalSignature_inj2 : types.

