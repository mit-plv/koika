Require Import Coq.Lists.List.
Require Export NArith.          (* Coq bug: If this isn't exported, other files can't import Vect.vo *)

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

Fixpoint index_to_nat {sz} (idx: index sz) {struct sz} : nat :=
  match sz return index sz -> nat with
  | 0 => fun idx => False_rect _ idx
  | S sz => fun idx => match idx with
                   | thisone => 0
                   | anotherone idx => S (index_to_nat idx)
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

Module Bits.
  Notation bits n := (vect bool n).
  Definition nil : bits 0 := vect_nil.
  Definition cons {n} (b: bool) (bs: bits n) := vect_cons b bs.
  Definition const sz (b: bool) : bits sz := vect_const sz b.
  Definition app {sz1 sz2} (bs1: bits sz1) (bs2: bits sz2) := vect_app bs1 bs2.
  Definition nth {n} (bs: bits n) (idx: index n) := vect_nth bs idx.
  Definition hd {n} (bs: bits (S n)) := vect_hd bs.
  Definition tl {n} (bs: bits (S n)) := vect_tl bs.
  Definition single (bs: bits 1) := vect_hd bs.
  Definition lsb {n} (bs: bits (S n)) := vect_last bs.
  Definition map {n} (f: bool -> bool) (bs: bits n) := vect_map f bs.
  Definition map2 {n} (f: bool -> bool -> bool) (bs1 bs2: bits n) := vect_map2 f bs1 bs2.

  Fixpoint to_nat {sz: nat} (bs: bits sz) : nat :=
    match sz return bits sz -> nat with
    | 0 => fun _ => 0
    | S n => fun bs => (if Bits.hd bs then 1 else 0) + 2 * to_nat (Bits.tl bs)
    end bs.

  Fixpoint to_N {sz: nat} (bs: bits sz) {struct sz} : N :=
    match sz return bits sz -> N with
    | O => fun _ => 0%N
    | S n => fun bs => ((if hd bs then 1 else 0) + 2 * to_N (tl bs))%N
    end bs.

  Fixpoint of_positive (sz: nat) (p: positive) {struct sz} : bits sz :=
    match sz with
    | 0 => nil
    | S sz =>
      match p with
      | xI p => cons true (of_positive sz p)
      | xO p => cons false (of_positive sz p)
      | xH => cons true (const sz false)
      end
    end.

  Definition of_N sz (n: N): bits sz :=
    match n with
    | N0 => const sz false
    | Npos p => of_positive sz p
    end.

  Definition to_index {sz} sz' (bs: bits sz) : option (index sz') :=
    index_of_nat sz' (to_nat bs).
End Bits.

Notation bits n := (Bits.bits n).
Notation "'Ob'" := Bits.nil (at level 7) : bits.
Notation "'w1' b" := (Bits.cons b Bits.nil) (at level 7, left associativity) : bits.
Notation "bs '~' b" := (Bits.cons b bs) (at level 7, left associativity, format "bs '~' b") : bits.
Notation "bs '~' 0" := (Bits.cons false bs) (at level 7, left associativity, format "bs '~' 0") : bits.
Notation "bs '~' 1" := (Bits.cons true bs) (at level 7, left associativity, format "bs '~' 1") : bits.
Global Open Scope bits.

Definition pow2 n :=
  Nat.pow 2 n.
