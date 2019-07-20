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

Fixpoint vect_of_list {T} (l: list T) : vect T (length l) :=
  match l with
  | nil => vect_nil
  | cons h t => vect_cons h (vect_of_list t)
  end.

Fixpoint vect_truncate_left {T sz} n (v: vect T (n + sz)) : vect T sz :=
  match n return vect T (n + sz) -> vect T sz with
  | 0 => fun v => v
  | S n => fun '(h, t) => vect_truncate_left n t
  end v.

Fixpoint vect_snoc {T sz} (t: T) (v: vect T sz) : vect T (S sz) :=
  match sz return vect T sz -> vect T (S sz) with
  | O => fun v => vect_cons t vect_nil
  | S sz => fun v => vect_cons (vect_hd v) (vect_snoc t (vect_tl v))
  end v.

Fixpoint vect_unsnoc {T sz} (v: vect T (S sz)) : T * vect T sz :=
  match sz return vect T (S sz) -> T * vect T sz with
  | O => fun v => (vect_hd v, vect_tl v)
  | S sz => fun v => let '(t, v') := vect_unsnoc (vect_tl v) in
                 (t, vect_cons (vect_hd v) v')
  end v.

Definition vect_cycle_l1 {T sz} (v: vect T sz) :=
  match sz return vect T sz -> vect T sz with
  | O => fun v => v
  | S sz => fun v => vect_snoc (vect_hd v) (vect_tl v)
  end v.

Definition vect_cycle_r1 {T sz} (v: vect T sz) :=
  match sz return vect T sz -> vect T sz with
  | O => fun v => v
  | S sz => fun v => let '(t, v') := vect_unsnoc v in
                 vect_cons t v'
  end v.

Fixpoint vect_repeat {A} (f: A -> A) n (v: A)
  : A :=
  match n with
  | O => v
  | S n => vect_repeat f n (f v)
  end.

Definition vect_cycle_l {T sz} n (v: vect T sz) :=
  vect_repeat vect_cycle_l1 n v.

Definition vect_cycle_r {T sz} n (v: vect T sz) :=
  vect_repeat vect_cycle_r1 n v.

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
  Definition zeroes sz := const sz false.
  Definition ones sz := const sz true.

  Definition lsr1 {sz} (b: bits sz) :=
    match sz return bits sz -> bits sz with
    | 0 => fun b => b
    | S _ => fun b => vect_snoc false (vect_tl b)
    end b.
  Definition lsl1 {sz} (b: bits sz) :=
    match sz return bits sz -> bits sz with
    | 0 => fun b => b
    | S _ => fun b => vect_cons false (snd (vect_unsnoc b))
    end b.
  Definition lsr {sz} nplaces (b: bits sz) :=
    vect_repeat lsr1 nplaces b.
  Definition lsl {sz} nplaces (b: bits sz) :=
    vect_repeat lsl1 nplaces b.

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

  Definition zero sz : bits sz := of_N sz N.zero.
  Definition one sz : bits sz := of_N sz N.one.

  Definition to_index {sz} sz' (bs: bits sz) : option (index sz') :=
    index_of_nat sz' (to_nat bs).

  Lemma single_cons :
    forall bs, cons (single bs) nil = bs.
  Proof. destruct bs as [ ? [ ] ]; reflexivity. Qed.

  Lemma cons_inj :
    forall {sz} b1 b2 (t1 t2: bits sz),
      cons b1 t1 = cons b2 t2 ->
      b1 = b2 /\ t1 = t2.
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Lemma single_inj:
    forall bs1 bs2,
      single bs1 = single bs2 ->
      bs1 = bs2.
  Proof.
    intros * Heq; rewrite <- (single_cons bs1), <- (single_cons bs2), Heq; reflexivity.
  Qed.
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
