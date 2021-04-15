(*! Utilities | Functions on Vect.index elements !*)
Require Coq.Logic.FinFun.
Require Import Koika.Common Koika.Member.
Require Export Koika.Vect.

Fixpoint all_indices (bound: nat) : vect (index bound) bound :=
  match bound as n return (vect (index n) n) with
  | 0 => vect_nil
  | S bound => vect_cons thisone (vect_map anotherone (all_indices bound))
  end.

Fixpoint all_indices_eqn bound:
  forall idx, vect_nth (all_indices bound) idx = idx.
Proof.
  destruct bound, idx; cbn.
  - reflexivity.
  - rewrite vect_nth_map.
    rewrite all_indices_eqn.
    reflexivity.
Defined.

Lemma all_indices_NoDup bound:
  vect_NoDup (all_indices bound).
Proof.
  induction bound; cbn; econstructor.
  - intro.
    apply vect_to_list_In in H.
    apply vect_map_In_ex in H.
    destruct H as [t (? & ?)]; discriminate.
  - setoid_rewrite vect_to_list_map.
    apply FinFun.Injective_map_NoDup.
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
  refine {| finite_index := index_to_nat;
            finite_elements := vect_to_list (all_indices n) |}.
  - intros; rewrite vect_to_list_nth, all_indices_eqn; reflexivity.
  - apply FinFun.Injective_map_NoDup.
    red; apply index_to_nat_injective.
    apply all_indices_NoDup.
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

Fixpoint List_nth_map_cast {A B} (f: A -> B) l:
  List.length l = List.length (List.map f l).
Proof. destruct l; cbn; auto. Defined.

Lemma List_nth_map {A B} (f: A -> B):
  forall l idx,
    f (List_nth l idx) =
    List_nth (List.map f l)
             ltac:(rewrite <- List_nth_map_cast; exact idx).
Proof.
  induction l; destruct idx; cbn;
    set (List_nth (List.map f l)) as x in *; clearbody x.
  - set (List_nth_map_cast _ _) as Heq in *; clearbody Heq.
    destruct Heq; reflexivity.
  - rewrite IHl; clear.
    set (List_nth_map_cast _ _) as Heq in *; clearbody Heq.
    destruct Heq; reflexivity.
Qed.

Lemma List_nth_firstn_1_skipn {A} (l: list A) a:
  List.firstn 1 (List.skipn (index_to_nat a) l) =
  [List_nth l a].
Proof.
  induction l; destruct a; cbn.
  - reflexivity.
  - specialize (IHl a).
    destruct (skipn _ _); inversion IHl; reflexivity.
Qed.

Lemma List_nth_skipn_cons_next {A}:
  forall (l: list A) idx,
    List_nth l idx :: (List.skipn (S (index_to_nat idx)) l) =
    List.skipn (index_to_nat idx) l.
Proof.
  induction l; destruct idx; cbn; try rewrite IHl; reflexivity.
Qed.

Lemma list_sum_member_le:
  forall l idx,
    List_nth l idx <=
    list_sum l.
Proof.
  induction l; destruct idx.
  - cbn; lia.
  - specialize (IHl a0); unfold list_sum, list_sum' in *; cbn; lia.
Qed.

Instance Show_index (n: nat) : Show (index n) :=
  { show x := show (index_to_nat x) }.
