Require Import Coq.Lists.List.
Require Import rv.Tactics.
Import ListNotations.

(*! List Helpers !*)

Ltac simplify_forall :=
  match goal with
  | H: Forall2 _ [] (_ :: _) |- _ => solve[inversion H]
  | H: Forall2 _ (_ :: _) [] |- _ => solve[inversion H]
  | H: Forall2 _ [] [] |- _ => solve[constructor]
  end.

Module ListHelpers.
   Lemma Forall2_setoid_refl :
     forall X (eq: X -> X -> Prop) xs,
     (forall x, eq x x) ->
     Forall2 eq xs xs.
   Proof.
     induction xs; auto.
   Qed.


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

  Lemma Forall2_impl : forall {X Y} {P: X -> Y -> Prop} {Q: X -> Y -> Prop}
                         {xs: list X} {ys: list Y},
      (forall x y, P x y -> Q x y) ->
      List.Forall2 P xs ys ->
      List.Forall2 Q xs ys.
  Proof.
    intros. induction H0; auto.
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

  Lemma Forall_app: forall {A} P (xs ys: list A),
    Forall P xs ->
    Forall P ys ->
    Forall P (xs ++ ys).
  Proof.
    induction xs; auto.
    intros.
    rewrite<-app_comm_cons.
    inversion H; subst.
    constructor; auto.
  Qed.

  Lemma NoDup_single_elem :
    forall {T} (x:T), NoDup [x].
  Proof.
    intros. constructor; auto.
    constructor.
  Qed.


  Lemma NoDup_map_inj:
    forall {A} {B} {C} (f: A -> B) (g: B -> C) (xs: list A),
    FinFun.Injective g ->
    NoDup (map f xs) ->
    NoDup (map (fun x => g (f x)) xs).
  Proof.
    intros. rewrite<-map_map.
    apply FinFun.Injective_map_NoDup; auto.
  Qed.

  Lemma NoDup_map_succ :
    forall {A} f (xs: list A),
    NoDup (map f xs) ->
    NoDup (map (fun x => S (f x)) xs).
  Proof.
    intros; apply NoDup_map_inj; auto.
    unfold FinFun.Injective; intros.
    lia.
  Qed.

  Lemma NoDup_map_plus:
    forall {A} f (xs: list A) n,
    NoDup (map f xs) ->
    NoDup (map (fun x => n + (f x)) xs).
  Proof.
    intros; apply NoDup_map_inj; auto.
    unfold FinFun.Injective; intros.
    lia.
  Qed.

  Lemma nth_error_app_map :
    forall {A} {B} (xs: list A) (ys: list B) f n z,
    nth_error ys n = Some z ->
    nth_error (map f xs ++ ys) (List.length xs + n) = Some z.
  Proof.
    intros. induction xs; auto.
  Qed.

  Lemma In_lt :
    forall {A} (xs: list A) v f,
    (forall x, v < f x) ->
    In v (map (fun x => f x) xs) -> False.
  Proof.
    induction xs; simpl in *; auto.
    intuition.
    - specialize H with (x := a); lia.
    - eapply IHxs; eauto.
  Qed.

  Lemma no_dup_increasing_app:
    forall xs ys ,
    (exists v, (forall x, (In x xs -> x < v)) /\
           (forall y, ((In y ys -> y >= v)))) ->
    NoDup xs ->
    NoDup ys ->
    NoDup (xs ++ ys).
  Proof.
    intros. induction xs.
    - simpl in *. auto.
    - simpl in *. apply NoDup_cons.
      + intuition.
        rewrite NoDup_cons_iff in *. propositional.
        apply in_app_or in H2. intuition.
        specialize H4 with (1 := or_introl eq_refl).
        specialize H5 with (1 := H). lia.
      + apply IHxs.
        * propositional. exists v; auto.
        * rewrite NoDup_cons_iff in H0; propositional; auto.
  Qed.

 Lemma cons_app :
    forall {A} (x: A) (xs: list A),
    x :: xs = [x] ++ xs.
  Proof.
    auto.
  Qed.

  Lemma map_nil : forall {A} {B} (f: A -> B),
      map f [] = [].
  Proof.
    auto.
  Qed.

  Lemma map_not_nil :
    forall {A B} (xs: list A) (f: A -> B),
    xs <> [] ->
    map f xs <> [].
  Proof.
    intuition.
    destruct xs; simpl in *; auto.
    congruence.
  Qed.

End ListHelpers.

Export ListHelpers.


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
