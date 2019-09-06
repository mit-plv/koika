Require Import SGA.Common SGA.Vect.

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
