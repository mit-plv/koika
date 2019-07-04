Require Import List.
Require Import SGA.Common SGA.Syntax.

Create HintDb types discriminated.
Hint Transparent not : types.

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

Record ExternalSignature :=
  FunSig { argSizes: list nat;
           retType: type }.

Lemma ExternalSignature_inj2 :
  forall (argSizes argSizes': list nat) (retType retType': type),
    FunSig argSizes retType =
    FunSig argSizes' retType' ->
    retType = retType'.
Proof. now inversion 1. Qed.

Hint Extern 10 => eapply @ExternalSignature_inj2 : types.

