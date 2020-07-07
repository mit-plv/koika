Require Import Coq.Lists.List.
Import ListNotations.

Ltac simplify_forall :=
  match goal with
  | H: Forall2 _ [] (_ :: _) |- _ => solve[inversion H]
  | H: Forall2 _ (_ :: _) [] |- _ => solve[inversion H]
  | H: Forall2 _ [] [] |- _ => solve[constructor]
  end.


Lemma Forall2_eq : forall {A} (xs ys: list A),
  List.Forall2 (@eq A) xs ys ->
  xs = ys.
Proof.
  induction xs; intros.
  - destruct ys; intuition; simplify_forall.
  - destruct ys; simpl in *; try simplify_forall.
    f_equal.
    + inversion H; auto.
    + apply IHxs; inversion H; auto.
Qed.

Lemma Forall2_compose : forall {X Y Z} {P: X -> Y -> Prop} {Q: Y -> Z -> Prop} {R: X -> Z -> Prop}
                          {xs: list X} {ys: list Y} {zs: list Z},
  (forall x y z, P x y -> Q y z -> R x z) ->
  List.Forall2 P xs ys ->
  List.Forall2 Q ys zs ->
  List.Forall2 R xs zs.
Proof.
  induction xs.
  - induction ys; induction zs; intuition; simplify_forall.
  - induction ys; intuition; try simplify_forall.
    generalize dependent zs.
    induction zs; intuition; try simplify_forall.
    inversion_clear H0; subst.
    inversion_clear H1; subst.
    constructor.
    + eapply H; eauto.
    + eapply IHxs; eauto.
Qed.
