Require Import Coq.Strings.String Coq.Lists.List.
Require Import SGA.Common.

Import ListNotations.

Inductive member {K: Type}: K -> list K -> Type :=
| MemberHd: forall k sig, member k (k :: sig)
| MemberTl: forall k k' sig, member k sig -> member k (k' :: sig).

(* https://github.com/coq/coq/issues/10749 *)
Definition eq_type {A} (a a': A) : Type :=
  eq a a'.

Definition mdestruct {K sig} {k: K} (m: member k sig)
  : match sig return member k sig -> Type with
    | [] => fun m => False
    | k' :: sig =>
      fun m => ({ eqn: (eq_type k k') & m = eq_rect _ _ (fun _ => MemberHd k sig) _ eqn m } +
             { m': member k sig & m = MemberTl k k' sig m' })%type
    end m.
  destruct m; cbn.
  - left; exists eq_refl; eauto.
  - right; eauto.
Defined.

Lemma member_In {K} (sig: list K):
  forall k, member k sig -> List.In k sig.
Proof.
  induction 1; firstorder.
Qed.

Fixpoint member_idx {K sig} {k: K} (m: member k sig) : nat :=
  match m with
  | MemberHd k sig => 0
  | MemberTl k k' sig m' => S (member_idx m')
  end.

Lemma member_idx_nth {K sig} (k: K) (m: member k sig) :
  List.nth_error sig (member_idx m) = Some k.
Proof.
  induction m; firstorder.
Qed.

Lemma nth_member {T}:
  forall (ls: list T) idx t,
    List.nth_error ls idx = Some t ->
    member t ls.
Proof.
  induction ls; destruct idx; cbn; inversion 1; subst;
    eauto using MemberHd, MemberTl.
Defined.

Lemma member_map {A B} (f: A -> B) a:
  forall ls,
    member a ls ->
    member (f a) (List.map f ls).
Proof.
  induction ls; cbn; intros m.
  - destruct (mdestruct m).
  - destruct (mdestruct m) as [(-> & Heq) | (m' & Heq)];
      subst; eauto using MemberHd, MemberTl.
Defined.

Lemma member_app_l {A} (a: A):
  forall ls ls',
    member a ls ->
    member a (ls ++ ls').
Proof.
  induction ls; cbn; intros ls' m.
  - destruct (mdestruct m).
  - destruct (mdestruct m) as [(-> & Heq) | (m' & Heq)];
      subst; eauto using MemberHd, MemberTl.
Defined.

Lemma member_app_r {A} (a: A):
  forall ls ls',
    member a ls' ->
    member a (ls ++ ls').
Proof.
  induction ls; cbn; eauto using MemberTl.
Defined.

Lemma member_NoDup {K} {sig: list K} k:
  EqDec K ->
  NoDup sig ->
  forall (m1 m2: member k sig),
    m1 = m2.
Proof.
  induction 2.
  - intros; destruct (mdestruct m1).
  - intros; destruct (mdestruct m1) as [(-> & ->) | (mem & ->)]; cbn.
    + intros; destruct (mdestruct m2) as [(? & ->) | (absurd & ->)]; cbn.
      * rewrite <- Eqdep_dec.eq_rect_eq_dec by apply eq_dec.
        reflexivity.
      * exfalso; apply member_In in absurd; auto.
    + intros; destruct (mdestruct m2) as [(-> & ->) | (? & ->)]; cbn.
      * exfalso; apply member_In in mem. auto.
      * f_equal; apply IHNoDup.
Qed.

Fixpoint mem {K} `{EqDec K} (k: K) sig {struct sig} : member k sig + (member k sig -> False).
  destruct sig.
  - right; inversion 1.
  - destruct (eq_dec k k0) as [Heq | Hneq].
    + subst. left. apply MemberHd.
    + destruct (mem _ _ k sig) as [m | ].
      * left. apply MemberTl. exact m.
      * right. inversion 1; congruence.
Defined.

Fixpoint find {K} (fn: K -> bool) sig {struct sig} : option { k: K & member k sig }.
  destruct sig.
  - right.
  - destruct (fn k) eqn:?.
    + left. eexists. apply MemberHd.
    + destruct (find _ fn sig) as [ (k' & m) | ].
      * left. eexists. apply MemberTl. eassumption.
      * right.
Defined.

Fixpoint assoc {K1 K2: Type} `{EqDec K1}
         (k1: K1) sig {struct sig} : option { k2: K2 & member (k1, k2) sig }.
Proof.
  destruct sig as [ | (k1' & k2) sig ].
  - right.
  - destruct (eq_dec k1 k1'); subst.
    + left. eexists. apply MemberHd.
    + destruct (assoc _ _ _ k1 sig) as [ (k2' & m) | ].
      * left. eexists. apply MemberTl. eassumption.
      * right.
Defined.

Class FiniteType {T} :=
  { finite_elems: list T;
    finite_nodup: List.NoDup finite_elems;
    finite_index: forall t: T, member t finite_elems }.
Arguments FiniteType: clear implicits.

Instance EqDec_FiniteType {T} `{FiniteType T} : EqDec T.
  econstructor; intros.
  destruct (PeanoNat.Nat.eq_dec (member_idx (finite_index t1)) (member_idx (finite_index t2))) as [ H' | H' ].
  - left.
    apply (f_equal (List.nth_error finite_elems)) in H'.
    rewrite !member_idx_nth in H'.
    congruence.
  - right.
    intros ->.
    congruence.
Qed.

Inductive FiniteType_norec (T: Type) :=
  | finite_type_norec : FiniteType_norec T.

Ltac FiniteType_t_member :=
  lazymatch goal with
  | [  |- forall _: _, member _ _ ] => let t := fresh "t" in intros t; destruct t
  | [  |- member ?r (_ :: _) ] => apply MemberTl
  | [  |- member ?r (_ ++ _) ] => apply member_app_r
  | [  |- member (?f ?r) ?l ] =>
    let t := type of r in
    apply member_app_l; apply member_map; pose proof (finite_type_norec t);
    (* Must call typeclasses eauto manually, because plain typeclass resolution
       doesn't operate in the current context (and so FiniteType_norec isn't
       taken into account). *)
    eapply (finite_index (T := t) (FiniteType := ltac:(typeclasses eauto)))
  | [  |- member ?r ?l ] => is_evar l; apply MemberHd
  | _ => idtac
  end.

Ltac FiniteType_t :=
  lazymatch goal with
  | [ H: FiniteType_norec ?T |- FiniteType ?T ] => fail "Type" T "is recursive"
  | [  |- FiniteType ?T ] =>
    econstructor;
    repeat FiniteType_t_member;
    match goal with
    | [  |- List.NoDup _ ] => repeat econstructor
    | _ => fail 2 "Could not prove finiteness of type" T
    end;
    match goal with
    | [  |- ~ List.In _ _ ] => solve [cbv; intuition discriminate]
    | _ => fail 2 "Could not prove side conditions for finiteness of type" T
    end
  end.

Hint Extern 1 (FiniteType _) => FiniteType_t : typeclass_instances.
