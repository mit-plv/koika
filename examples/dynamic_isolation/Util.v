Require Import Coq.Lists.List.
Require Import dynamic_isolation.Tactics.
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

Lemma not_exists_some_is_none :
  forall {A} (opt: option A),
  not (exists a, opt = Some a) ->
  opt = None.
Proof.
  intros. destruct opt; auto.
  unfold not in *. assert_false.
  apply H. exists a; auto.
Qed.

Definition maybe_holds {T} (p:T -> Prop) : option T -> Prop :=
fun mt => match mt with
       | Some t => p t
       | None => True
       end.

Lemma holds_in_none_eq : forall T (p: T -> Prop) mt,
    mt = None ->
    maybe_holds p mt.
Proof.
  intros; subst.
  simpl; auto.
Qed.

Lemma holds_in_some : forall T (p:T -> Prop) (v:T),
    p v ->
    maybe_holds p (Some v).
Proof.
  simpl; auto.
Qed.

Lemma holds_in_some_eq : forall T (p:T -> Prop) (v:T) mt,
    mt = Some v ->
    p v ->
    maybe_holds p mt.
Proof.
  intros; subst.
  simpl; auto.
Qed.

Lemma holds_some_inv_eq : forall T (p: T -> Prop) mt v,

    mt = Some v ->
    maybe_holds p mt ->
    p v.
Proof.
  intros; subst.
  auto.
Qed.

Lemma pred_weaken : forall T (p p': T -> Prop) mt,
    maybe_holds p mt ->
    (forall t, p t -> p' t) ->
    maybe_holds p' mt.
Proof.
  unfold maybe_holds; destruct mt; eauto.
Qed.

Definition maybe_eq {T} (mv : option T) (v : T) : Prop :=
  maybe_holds (eq v) mv.

Notation "mv =?= v" := (maybe_eq mv v) (at level 20, v at level 50).
