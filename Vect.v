Require Import Coq.Lists.List.

Fixpoint index n : Type :=
  match n with
  | 0 => False
  | S n => unit + index n
  end.

Fixpoint vect T n : Type :=
  match n with
  | 0 => unit
  | S n => (T * @vect T n)%type
  end.

Definition vect_hd {T n} (v: vect T (S n)) : T :=
  fst v.

Definition vect_cons {T n} (t: T) (v: vect T n) : vect T (S n) :=
  (t, v).

Fixpoint vect_last {T n} (v: vect T (S n)) : T :=
  match n return vect T (S n) -> T with
  | O => fun v => (fst v)
  | S _ => fun v => vect_last (snd v)
  end v.

Fixpoint vect_map {T T' n} (f: T -> T') (v: vect T n) : vect T' n :=
  match n return vect T n -> vect T' n with
  | O => fun _ => tt
  | S _ => fun '(hd, tl) => (f hd, vect_map f tl)
  end v.

Fixpoint vect_zip {T1 T2 n} (v1: vect T1 n) (v2: vect T2 n) : vect (T1 * T2) n :=
  match n return vect T1 n -> vect T2 n -> vect (T1 * T2) n with
  | O => fun _ _ => tt
  | S _ => fun '(hd1, tl1) '(hd2, tl2) => ((hd1,  hd2), vect_zip tl1 tl2)
  end v1 v2.

Definition vect_map2 {T1 T2 T n} (f: T1 -> T2 -> T) (v1: vect T1 n) (v2: vect T2 n) : vect T n :=
  vect_map (fun '(b1, b2) => f b1 b2) (vect_zip v1 v2).

Fixpoint vect_fold_left {A T n} (f: A -> T -> A) (a0: A) (v: vect T n) : A :=
  match n return vect T n -> A with
  | O => fun _ => a0
  | S _ => fun '(hd, tl) => f (vect_fold_left f a0 tl) hd
  end v.

Definition vect_to_list {T n} (v: vect T n) : list T :=
  vect_fold_left (fun acc t => List.cons t acc) List.nil v.

Notation bits n := (vect bool n).
Definition bits_nil : bits 0 := tt.
Definition bits_hd {n} (bs: bits (S n)) := vect_hd bs.
Definition bits_cons {n} (b: bool) (bs: bits n) := vect_cons b bs.
Definition bits_single (bs: bits 1) := vect_hd bs.
Definition bits_lsb {n} (bs: bits (S n)) := vect_last bs.
Definition bits_map {n} (f: bool -> bool) (bs: bits n) := vect_map f bs.
Definition bits_map2 {n} (f: bool -> bool -> bool) (bs1 bs2: bits n) := vect_map2 f bs1 bs2.

Notation "'w0'" := bits_nil (at level 5) : bits.
Notation "'w1' b" := (bits_cons b bits_nil) (at level 5) : bits.
Notation "b '~' bs" := (bits_cons b bs) (at level 5, right associativity, format "b '~' bs") : bits.
Notation "0 '~' bs" := (bits_cons false bs) (at level 5, right associativity, format "0 '~' bs") : bits.
Notation "1 '~' bs" := (bits_cons true bs) (at level 5, right associativity, format "1 '~' bs") : bits.
Global Open Scope bits.
