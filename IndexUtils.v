Require Import Coq.Logic.FinFun.
Require Import SGA.Common SGA.Vect SGA.Member.

Fixpoint all_indices (bound: nat) : vect (index bound) bound :=
  match bound as n return (vect (index n) n) with
  | 0 => vect_nil
  | S bound => (thisone, vect_map anotherone (all_indices bound))
  end.

Lemma all_indices_eqn bound:
  forall idx, vect_nth (all_indices bound) idx = idx.
Proof.
  induction bound; destruct idx; cbn.
  - reflexivity.
  - rewrite vect_nth_map.
    rewrite IHbound.
    reflexivity.
Qed.

Lemma all_indices_NoDup bound:
  List.NoDup (vect_to_list (all_indices bound)).
Proof.
  induction bound; cbn; econstructor.
  - intro.
    apply vect_to_list_In in H.
    apply vect_map_In_ex in H.
    destruct H as [t (? & ?)]; discriminate.
  - setoid_rewrite vect_to_list_map.
    apply Injective_map_NoDup.
    + red; inversion 1; reflexivity.
    + eassumption.
Qed.

Lemma all_indices_surjective bound:
  forall idx, member idx (vect_to_list (all_indices bound)).
Proof.
  intros.
  eapply nth_member.
  rewrite vect_to_list_nth.
  f_equal.
  apply all_indices_eqn.
Defined.

Instance FiniteType_index {n} : FiniteType (Vect.index n).
Proof.
  refine {| finite_elems := vect_to_list (all_indices n) |}.
  - apply all_indices_NoDup.
  - apply all_indices_surjective.
Defined.

Fixpoint Vector_find {K: Type} {n: nat} {EQ: EqDec K} (k: K) (v: Vector.t K n) {struct n} : option (Vect.index n).
Proof.
  destruct n.
  - exact None.
  - destruct (eq_dec k (Vector.hd v)).
    + exact (Some thisone).
    + destruct (Vector_find K n EQ k (Vector.tl v)).
      * exact (Some (anotherone i)).
      * exact None.
Defined.

Fixpoint Vector_assoc {K V: Type} {n: nat} {EQ: EqDec K} (k: K) (v: Vector.t (K * V) n) {struct n} : option (Vect.index n).
Proof.
  destruct n.
  - exact None.
  - destruct (eq_dec k (fst (Vector.hd v))).
    + exact (Some thisone).
    + destruct (Vector_assoc K V n EQ k (Vector.tl v)).
      * exact (Some (anotherone i)).
      * exact None.
Defined.

Fixpoint List_assoc {K V: Type} {EQ: EqDec K} (k: K) (l: list (K * V)) {struct l} : option (Vect.index (List.length l)).
Proof.
  destruct l as [| h l].
  - exact None.
  - destruct (eq_dec k (fst h)).
    + exact (Some thisone).
    + destruct (List_assoc K V EQ k l).
      * exact (Some (anotherone i)).
      * exact None.
Defined.

Fixpoint Vector_nth {K: Type} {n: nat} (v: Vector.t K n) (idx: Vect.index n) {struct n} : K.
Proof.
  destruct n; destruct idx.
  - exact (Vector.hd v).
  - exact (Vector_nth K n (Vector.tl v) a).
Defined.

Fixpoint List_nth {K: Type} (l: list K) (idx: Vect.index (List.length l)) {struct l} : K.
Proof.
  destruct l as [| h l]; destruct idx.
  - exact h.
  - exact (List_nth K l a).
Defined.
