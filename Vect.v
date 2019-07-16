Require Import Coq.Lists.List.

Inductive index' {A} := thisone | anotherone (a: A).
Arguments index': clear implicits.

Fixpoint index n : Type :=
  match n with
  | 0 => False
  | S n => index' (index n)
  end.

Fixpoint index_of_nat (sz n: nat) : option (index sz) :=
  match sz with
  | 0 => None
  | S sz =>
    match n with
    | 0 => Some thisone
    | S n => match (index_of_nat sz n) with
            | Some idx => Some (anotherone idx)
            | None => None
            end
    end
  end.

Fixpoint nat_of_index {sz} (idx: index sz) {struct sz} : nat :=
  match sz return index sz -> nat with
  | 0 => fun idx => False_rect _ idx
  | S sz => fun idx => match idx with
                   | thisone => 0
                   | anotherone idx => S (nat_of_index idx)
                   end
  end idx.

Fixpoint vect T n : Type :=
  match n with
  | 0 => unit
  | S n => (T * @vect T n)%type
  end.

Definition vect_hd {T n} (v: vect T (S n)) : T :=
  fst v.

Definition vect_tl {T n} (v: vect T (S n)) : vect T n :=
  snd v.

Definition vect_nil {T} : vect T 0 := tt.

Definition vect_cons {T n} (t: T) (v: vect T n) : vect T (S n) :=
  (t, v).

Fixpoint vect_const {T} sz (t: T) : vect T sz :=
  match sz with
  | 0 => vect_nil
  | S sz => (t, vect_const sz t)
  end.

Fixpoint vect_app {T} {sz1 sz2} (bs1: vect T sz1) (bs2: vect T sz2) {struct sz1} : vect T (sz1 + sz2) :=
  match sz1 as n return (vect T n -> vect T (n + sz2)) with
  | 0 => fun _ => bs2
  | S sz1 => fun bs1 => vect_cons (vect_hd bs1) (vect_app (vect_tl bs1) bs2)
  end bs1.

Fixpoint vect_nth {T n} (v: vect T n) (idx: index n) {struct n} : T :=
  match n return (vect T n -> index n -> T) with
  | 0 => fun _ idx => False_rect _ idx
  | S n => fun v idx =>
            match idx with
            | thisone => vect_hd v
            | anotherone idx => vect_nth (vect_tl v) idx
            end
  end v idx.

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
Definition bits_nil : bits 0 := vect_nil.
Definition bits_cons {n} (b: bool) (bs: bits n) := vect_cons b bs.
Definition bits_const sz (b: bool) : bits sz := vect_const sz b.
Definition bits_app {sz1 sz2} (bs1: bits sz1) (bs2: bits sz2) := vect_app bs1 bs2.
Definition bits_nth {n} (bs: bits n) (idx: index n) := vect_nth bs idx.
Definition bits_hd {n} (bs: bits (S n)) := vect_hd bs.
Definition bits_single (bs: bits 1) := vect_hd bs.
Definition bits_lsb {n} (bs: bits (S n)) := vect_last bs.
Definition bits_map {n} (f: bool -> bool) (bs: bits n) := vect_map f bs.
Definition bits_map2 {n} (f: bool -> bool -> bool) (bs1 bs2: bits n) := vect_map2 f bs1 bs2.

Fixpoint bits_to_nat' {sz: nat} (acc: nat) (bs: bits sz) : nat :=
  match sz return bits sz -> nat with
  | 0 => fun _ => acc
  | S n => fun bs => bits_to_nat' (2 * acc + (if fst bs then 1 else 0)) (snd bs)
  end bs.

Definition bits_to_nat {sz: nat} (bs: bits sz) : nat :=
  bits_to_nat' 0 bs.

(* Compute (bits_to_nat 1~0~0~1~1~0~w0). *)

Definition index_of_bits {sz} sz' (bs: bits sz) : option (index sz') :=
  index_of_nat sz' (bits_to_nat bs).

Definition pow2 n :=
  Nat.pow 2 n.

Notation "'w0'" := bits_nil (at level 5) : bits.
Notation "'w1' b" := (bits_cons b bits_nil) (at level 5) : bits.
Notation "b '~' bs" := (bits_cons b bs) (at level 5, right associativity, format "b '~' bs") : bits.
Notation "0 '~' bs" := (bits_cons false bs) (at level 5, right associativity, format "0 '~' bs") : bits.
Notation "1 '~' bs" := (bits_cons true bs) (at level 5, right associativity, format "1 '~' bs") : bits.
Global Open Scope bits.
