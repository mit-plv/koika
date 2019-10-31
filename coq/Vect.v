Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Export Coq.NArith.NArith.          (* Coq bug: If this isn't exported, other files can't import Vect.vo *)
Require Import Koika.EqDec.

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

Definition index_cast n n' (eq: n = n') (idx: index n) : index n' :=
  ltac:(subst; assumption).

Lemma index_to_nat_injective {n: nat}:
  forall x y : index n,
    index_to_nat x = index_to_nat y ->
    x = y.
Proof.
  induction n; destruct x, y; cbn; inversion 1.
  - reflexivity.
  - f_equal; eauto.
Qed.

Lemma index_to_nat_bounded {sz}:
  forall (idx: index sz), index_to_nat idx < sz.
Proof.
  induction sz; cbn; destruct idx; auto with arith.
Qed.

Lemma index_of_nat_bounded {sz n}:
  n < sz -> exists idx, index_of_nat sz n = Some idx.
Proof.
  revert n; induction sz; destruct n; cbn; try solve [inversion 1].
  - eauto.
  - intros Hlt.
    destruct (IHsz n ltac:(auto with arith)) as [ idx0 Heq ].
    eexists; rewrite Heq; reflexivity.
Qed.

Lemma index_to_nat_of_nat {sz}:
  forall n (idx: index sz),
    index_of_nat sz n = Some idx ->
    index_to_nat idx = n.
Proof.
  induction sz; cbn.
  - destruct idx.
  - destruct n.
    + inversion 1; reflexivity.
    + intros idx Heq.
      destruct (index_of_nat sz n) eqn:?; try discriminate.
      inversion Heq; erewrite IHsz; eauto.
Qed.

Lemma index_of_nat_to_nat {sz}:
  forall (idx: index sz),
    index_of_nat sz (index_to_nat idx) = Some idx.
Proof.
  induction sz; cbn; destruct idx.
  - reflexivity.
  - rewrite IHsz; reflexivity.
Qed.

Local Set Primitive Projections.
Inductive vect_nil_t {T: Type} := _vect_nil.
Record vect_cons_t {A B: Type} := _vect_cons { vhd: A; vtl: B }.
Arguments vect_nil_t : clear implicits.
Arguments vect_cons_t : clear implicits.
Arguments _vect_cons {A B} vhd vtl : assert.

Fixpoint vect T n : Type :=
  match n with
  | 0 => vect_nil_t T
  | S n => vect_cons_t T (@vect T n)
  end.

Definition vect_hd {T n} (v: vect T (S n)) : T :=
  v.(vhd).

Definition vect_hd_default {T n} (t: T) (v: vect T n) : T :=
  match n return vect T n -> T with
  | 0 => fun _ => t
  | S n => fun v => vect_hd v
  end v.

Definition vect_tl {T n} (v: vect T (S n)) : vect T n :=
  v.(vtl).

Definition vect_nil {T} : vect T 0 := _vect_nil.

Definition vect_cons {T n} (t: T) (v: vect T n) : vect T (S n) :=
  {| vhd := t; vtl := v |}.

Lemma vect_cons_hd_tl {T sz}:
  forall (v: vect T (S sz)),
    vect_cons (vect_hd v) (vect_tl v) = v.
Proof.
  unfold vect_hd, vect_tl.
  reflexivity.
Qed.

Fixpoint vect_const {T} sz (t: T) : vect T sz :=
  match sz with
  | 0 => vect_nil
  | S sz => vect_cons t (vect_const sz t)
  end.

Fixpoint vect_app {T} {sz1 sz2} (bs1: vect T sz1) (bs2: vect T sz2) {struct sz1} : vect T (sz1 + sz2) :=
  match sz1 as n return (vect T n -> vect T (n + sz2)) with
  | 0 => fun _ => bs2
  | S sz1 => fun bs1 => vect_cons (vect_hd bs1) (vect_app (vect_tl bs1) bs2)
  end bs1.

Fixpoint vect_app_nil_cast n:
  n = n + 0.
Proof. destruct n; cbn; auto. Defined.

Lemma vect_app_nil :
  forall {T sz} (v: vect T sz) (v0: vect T 0),
    vect_app v v0 =
    ltac:(rewrite <- vect_app_nil_cast; exact v).
Proof.
  destruct v0.
  induction sz; destruct v; cbn.
  - reflexivity.
  - rewrite IHsz.
    unfold f_equal_nat, f_equal.
    rewrite <- vect_app_nil_cast; reflexivity.
Defined.

Fixpoint vect_split {T} {sz1 sz2} (v: vect T (sz1 + sz2)) {struct sz1} : vect T sz1 * vect T sz2 :=
  match sz1 as n return (vect T (n + sz2) -> vect T n * vect T sz2) with
  | 0 => fun v => (vect_nil, v)
  | S sz1 =>
    fun v => let '(v1, v2) := vect_split (vect_tl v) in
          (vect_cons (vect_hd v) v1, v2)
  end v.

Lemma vect_app_split {T} {sz1 sz2}:
  forall (v: vect T (sz1 + sz2)),
    vect_app (fst (vect_split v)) (snd (vect_split v)) = v.
Proof.
  induction sz1; cbn; intros.
  - reflexivity.
  - rewrite (surjective_pairing (vect_split _)).
    cbn. rewrite IHsz1, vect_cons_hd_tl. reflexivity.
Qed.

Lemma vect_split_app {T} {sz1 sz2}:
  forall (v1: vect T sz1) (v2: vect T sz2),
    vect_split (vect_app v1 v2) = (v1, v2).
Proof.
  induction sz1; destruct v1; cbn; intros.
  - reflexivity.
  - rewrite IHsz1; reflexivity.
Qed.

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
  | O => fun v => vect_hd v
  | S _ => fun v => vect_last (vect_tl v)
  end v.

Definition vect_last_default {T n} (t: T) (v: vect T n) : T :=
  match n return vect T n -> T with
  | 0 => fun _ => t
  | S n => fun v => vect_last v
  end v.

Fixpoint vect_map {T T' n} (f: T -> T') (v: vect T n) : vect T' n :=
  match n return vect T n -> vect T' n with
  | O => fun _ => vect_nil
  | S _ => fun v => vect_cons (f (vect_hd v)) (vect_map f (vect_tl v))
  end v.

Lemma vect_nth_map {T T' sz} (f: T -> T'):
  forall (v: vect T sz) idx,
    vect_nth (vect_map f v) idx = f (vect_nth v idx).
Proof.
  induction sz; destruct v, idx; cbn; auto.
Qed.

Fixpoint vect_zip {T1 T2 n} (v1: vect T1 n) (v2: vect T2 n) : vect (T1 * T2) n :=
  match n return vect T1 n -> vect T2 n -> vect (T1 * T2) n with
  | O => fun _ _ => vect_nil
  | S _ => fun v1 v2 => vect_cons (vect_hd v1,  vect_hd v2)
                              (vect_zip (vect_tl v1) (vect_tl v2))
  end v1 v2.

Definition vect_map2 {T1 T2 T n} (f: T1 -> T2 -> T) (v1: vect T1 n) (v2: vect T2 n) : vect T n :=
  vect_map (fun '(b1, b2) => f b1 b2) (vect_zip v1 v2).

Fixpoint vect_fold_left {A T n} (f: A -> T -> A) (a0: A) (v: vect T n) : A :=
  match n return vect T n -> A with
  | O => fun _ => a0
  | S _ => fun v => f (vect_fold_left f a0 (vect_tl v)) (vect_hd v)
  end v.

Fixpoint vect_truncate_left {T sz} n (v: vect T (n + sz)) : vect T sz :=
  match n return vect T (n + sz) -> vect T sz with
  | 0 => fun v => v
  | S n => fun v => vect_truncate_left n (vect_tl v)
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

Fixpoint vect_skipn_cast n:
  n = n - 0.
Proof. destruct n; cbn; auto. Defined.

Fixpoint vect_skipn {T sz} (n: nat) (v: vect T sz) : vect T (sz - n) :=
  match n with
  | 0 => ltac:(rewrite <- (vect_skipn_cast sz); exact v)
  | S n' => match sz return vect T sz -> vect T (sz - S n') with
           | 0 => fun v => v
           | S sz' => fun v => vect_skipn n' (vect_tl v)
           end v
  end.

Fixpoint vect_firstn {T sz} (n: nat) (v: vect T sz) : vect T (min n sz) :=
  match n with
  | 0 => vect_nil
  | S n' => match sz return vect T sz -> vect T (min (S n') sz) with
           | 0 => fun v => v
           | S sz' => fun v => vect_cons (vect_hd v) (vect_firstn n' (vect_tl v))
           end v
  end.

Fixpoint vect_firstn_id_cast sz:
  Nat.min sz sz = sz.
Proof. destruct sz; cbn; auto. Defined.

Lemma vect_firstn_id :
  forall {T sz} (v: vect T sz),
    vect_firstn sz v =
    ltac:(rewrite (vect_firstn_id_cast sz); exact v).
Proof.
  induction sz; destruct v.
  - reflexivity.
  - cbn.
    rewrite IHsz.
    unfold f_equal_nat, f_equal;
      rewrite vect_firstn_id_cast; reflexivity.
Qed.

Fixpoint vect_firstn_plus_cast sz n:
  Nat.min n (n + sz) = n.
Proof. destruct n; cbn; eauto. Defined.

Definition vect_firstn_plus {T sz} (n: nat) (v: vect T (n + sz)) : vect T n :=
  ltac:(rewrite <- (vect_firstn_plus_cast sz n); exact (vect_firstn n v)).

Lemma vect_firstn_plus_eqn {T sz sz'}:
  forall hd (v: vect T (sz + sz')),
    vect_firstn_plus (S sz) (vect_cons hd v) =
    vect_cons hd (vect_firstn_plus sz v).
Proof.
  unfold vect_firstn_plus; cbn.
  rewrite <- (vect_firstn_plus_cast sz' sz); reflexivity.
Qed.

Lemma vect_firstn_plus_app {T sz n}:
  forall (prefix: vect T n) (v: vect T sz),
    vect_firstn_plus n (vect_app prefix v) = prefix.
Proof.
  induction n; destruct prefix; cbn; intros.
  - destruct sz; reflexivity.
  - rewrite vect_firstn_plus_eqn, IHn.
    reflexivity.
Qed.

Fixpoint vect_skipn_plus_cast sz n:
  n + sz - n = sz.
Proof. destruct n, sz; cbn; auto. Defined.

Definition vect_skipn_plus {T sz} (n: nat) (v: vect T (n + sz)) : vect T sz :=
  ltac:(rewrite <- (vect_skipn_plus_cast sz n); exact (vect_skipn n v)).

Lemma vect_skipn_plus_eqn {T sz sz'}:
  forall hd (v: vect T (sz + sz')),
    vect_skipn_plus (S sz) (vect_cons hd v) =
    vect_skipn_plus sz v.
Proof.
  unfold vect_skipn_plus; cbn; intros.
  destruct sz'; try rewrite <- (vect_skipn_plus_cast 0 sz); reflexivity.
Qed.

Lemma vect_skipn_plus_app {T sz n}:
  forall (prefix: vect T n) (v: vect T sz),
    vect_skipn_plus n (vect_app prefix v) = v.
Proof.
  induction n; cbn; intros.
  - destruct sz; reflexivity.
  - rewrite vect_skipn_plus_eqn.
    eauto.
Qed.

Lemma vect_skipn_skipn_plus :
  forall {T sz} (n: nat) (v: vect T (n + sz)),
    vect_skipn n v =
    ltac:(rewrite (vect_skipn_plus_cast sz n); exact (vect_skipn_plus n v)).
Proof. unfold vect_skipn_plus; intros; destruct vect_skipn_plus_cast; reflexivity. Qed.

Lemma vect_split_firstn_skipn :
  forall {T sz sz'} (v: vect T (sz + sz')),
    vect_split v =
    (vect_firstn_plus sz v, vect_skipn_plus sz v).
Proof.
  induction sz, sz'; cbn; destruct v; cbn;
    try rewrite <- Eqdep_dec.eq_rect_eq_dec by apply eq_dec;
    auto; rewrite IHsz; cbn;
      setoid_rewrite vect_firstn_plus_eqn;
      setoid_rewrite vect_skipn_plus_eqn;
      reflexivity.
Qed.

Fixpoint vect_extend_beginning_cast' x y:
  x + S y = S (x + y).
Proof. destruct x; cbn; auto. Defined.

Fixpoint vect_extend_beginning_cast sz sz':
  sz' - sz + sz = Nat.max sz sz'.
Proof.
  destruct sz, sz'; cbn; auto.
  cbn; rewrite <- vect_extend_beginning_cast; apply vect_extend_beginning_cast'.
Defined.

Definition vect_extend_beginning {T sz} (v: vect T sz) (sz': nat) (t: T) : vect T (Nat.max sz sz') :=
  ltac:(rewrite <- (vect_extend_beginning_cast sz sz'); exact (vect_app (vect_const (sz' - sz) t) v)).

Fixpoint vect_extend_end_cast sz sz':
  sz + (sz' - sz) = Nat.max sz sz'.
Proof. destruct sz, sz'; cbn; auto. Defined.

Definition vect_extend_end {T sz} (v: vect T sz) (sz': nat) (t: T) : vect T (Nat.max sz sz') :=
  ltac:(rewrite <- (vect_extend_end_cast sz sz'); exact (vect_app v (vect_const (sz' - sz) t))).

Fixpoint vect_extend_end_firstn_cast sz sz':
  Nat.max (Nat.min sz sz') sz = sz.
Proof. destruct sz, sz'; cbn; auto. Defined.

Definition vect_extend_end_firstn {T sz sz'} (v: vect T (Nat.min sz sz')) (t: T) : vect T sz :=
  ltac:(rewrite <- (vect_extend_end_firstn_cast sz sz'); exact (vect_extend_end v sz t)).

Lemma vect_extend_end_firstn_simpl :
  forall {T sz} (v: vect T sz) n b,
  forall (eqn: Nat.min n sz = n),
    vect_extend_end_firstn (vect_firstn n v) b =
    ltac:(rewrite <- eqn; exact (vect_firstn n v)).
Proof.
  unfold vect_extend_end_firstn, vect_extend_end; intros.
  rewrite <- eq_trans_rew_distr.
  set (eq_trans _ _) as Heq; clearbody Heq.
  revert Heq; replace (n - Nat.min n sz) with 0 by omega; intros.
  rewrite vect_app_nil.
  rewrite <- eq_trans_rew_distr.
  set (eq_trans _ _) as Heq'; clearbody Heq'.
  apply eq_rect_eqdec_irrel.
Qed.

Fixpoint vect_find {T sz} (f: T -> bool) (v: vect T sz) : option T :=
  match sz return vect T sz -> option T with
  | 0 => fun _ => None
  | S n => fun v => if f (vect_hd v) then Some (vect_hd v)
                else vect_find f (vect_tl v)
  end v.

Fixpoint vect_find_index {T sz} (f: T -> bool) (v: vect T sz) : option (index sz) :=
  match sz return vect T sz -> option (index sz) with
  | 0 => fun _ => None
  | S n => fun v => if f (vect_hd v) then Some thisone
                else match vect_find_index f (vect_tl v) with
                     | Some idx => Some (anotherone idx)
                     | None => None
                     end
  end v.

Definition vect_index {T sz} {EQ: EqDec T} (k: T) (v: vect T sz) : option (index sz) :=
  vect_find_index (fun t => beq_dec t k) v.

Lemma vect_nth_index {T sz} {EQ: EqDec T}:
  forall (t: T) (v: vect T sz) (idx: index sz),
    vect_index t v = Some idx ->
    vect_nth v idx = t.
Proof.
  induction sz.
  - destruct idx.
  - cbn; unfold beq_dec; intros t v idx Heq;
      destruct (eq_dec (vect_hd v) t); subst.
        inversion Heq; subst.
    + reflexivity.
    + destruct (vect_find_index _ _) eqn:?; inversion Heq; subst; eauto.
Qed.

Lemma vect_nth_index_None {T sz} {EQ: EqDec T}:
  forall (t: T) (v: vect T sz),
    vect_index t v = None ->
    forall idx, vect_nth v idx <> t.
Proof.
  induction sz.
  - destruct idx.
  - cbn; unfold beq_dec; intros t v Heq idx;
      destruct (eq_dec (vect_hd v) t); subst; try discriminate;
        destruct idx.
    + assumption.
    + destruct (vect_find_index _ _) eqn:?; try discriminate; eauto.
Qed.

Definition vect_In {T sz} t (v: vect T sz) : Prop :=
  vect_fold_left (fun acc t' => acc \/ t = t') False v.

Lemma vect_map_In {T T' sz} (f: T -> T'):
  forall t (v: vect T sz),
    vect_In t v -> vect_In (f t) (vect_map f v).
Proof.
  induction sz; destruct v; cbn;
    firstorder (subst; firstorder).
Qed.

Lemma vect_map_In_ex {T T' sz} (f: T -> T'):
  forall t' (v: vect T sz),
    vect_In t' (vect_map f v) -> (exists t, t' = f t /\ vect_In t v).
Proof.
  induction sz; destruct v; cbn.
  - destruct 1.
  - firstorder.
Qed.

Lemma vect_map_In_iff {T T' sz} (f: T -> T'):
  forall t' (v: vect T sz),
    (exists t, t' = f t /\ vect_In t v) <-> vect_In t' (vect_map f v).
Proof.
  split.
  - intros [t (-> & H)]; eauto using vect_map_In.
  - apply vect_map_In_ex.
Qed.

Section Conversions.
  Fixpoint vect_of_list {T} (l: list T) : vect T (length l) :=
    match l with
    | nil => vect_nil
    | cons h t => vect_cons h (vect_of_list t)
    end.

  Definition vect_to_list {T n} (v: vect T n) : list T :=
    vect_fold_left (fun acc t => List.cons t acc) List.nil v.

  Lemma vect_to_list_inj T :
    forall sz (v1 v2: vect T sz),
      vect_to_list v1 = vect_to_list v2 ->
      v1 = v2.
  Proof.
    induction sz; destruct v1, v2; cbn.
    - reflexivity.
    - inversion 1; subst; f_equal; apply IHsz; eassumption.
  Qed.

  Lemma vect_to_list_In {T sz} :
    forall t (v: vect T sz),
      vect_In t v <-> List.In t (vect_to_list v).
  Proof.
    induction sz; destruct v; cbn.
    - reflexivity.
    - setoid_rewrite IHsz.
      firstorder.
  Qed.

  Lemma vect_to_list_app {T sz sz'}:
    forall (v: vect T sz) (v': vect T sz'),
      vect_to_list (vect_app v v') =
      List.app (vect_to_list v) (vect_to_list v').
  Proof.
    induction sz; destruct v; cbn; intros;
      try setoid_rewrite IHsz; reflexivity.
  Qed.

  Lemma vect_to_list_nth {T sz}:
    forall (v: vect T sz) idx,
      List.nth_error (vect_to_list v) (index_to_nat idx) =
      Some (vect_nth v idx).
  Proof.
    induction sz; destruct v, idx; cbn.
    - reflexivity.
    - setoid_rewrite IHsz; reflexivity.
  Qed.

  Lemma vect_to_list_length {T sz}:
    forall (v: vect T sz),
      List.length (vect_to_list v) = sz.
  Proof.
    induction sz; cbn; intros.
    - reflexivity.
    - f_equal; apply IHsz; assumption.
  Qed.

  Lemma vect_to_list_eq_rect {T sz sz'} :
    forall (v: vect T sz) (pr: sz = sz'),
      vect_to_list (eq_rect _ _ v _ pr) = vect_to_list v.
  Proof. destruct pr; reflexivity. Defined.

  Fixpoint vect_to_list_firstn {T sz}:
    forall n (v: vect T sz),
      vect_to_list (vect_firstn n v) =
      List.firstn n (vect_to_list v).
  Proof.
    destruct n, sz; cbn in *; try reflexivity; destruct v.
    setoid_rewrite vect_to_list_firstn.
    reflexivity.
  Qed.

  Fixpoint vect_to_list_skipn {T sz}:
    forall n (v: vect T sz),
      vect_to_list (vect_skipn n v) =
      List.skipn n (vect_to_list v).
  Proof.
    destruct n, sz; cbn in *; try reflexivity; destruct v.
    setoid_rewrite vect_to_list_skipn.
    reflexivity.
  Qed.

  Fixpoint const {T} (n: nat) (t: T) :=
    match n with
    | O => List.nil
    | S n => List.cons t (const n t)
    end.

  Lemma vect_to_list_const {T}:
    forall n (t: T),
      vect_to_list (vect_const n t) =
      const n t.
  Proof.
    induction n; cbn; try setoid_rewrite IHn; reflexivity.
  Qed.

  Lemma vect_to_list_map {T T' sz} (f: T -> T'):
    forall (v: vect T sz),
      vect_to_list (vect_map f v) = List.map f (vect_to_list v).
  Proof.
    induction sz; destruct v; cbn.
    - reflexivity.
    - setoid_rewrite IHsz; reflexivity.
  Qed.
End Conversions.

Hint Rewrite @vect_to_list_eq_rect : vect_to_list.
Hint Rewrite @vect_to_list_app : vect_to_list.
Hint Rewrite @vect_to_list_firstn : vect_to_list.
Hint Rewrite @vect_to_list_skipn : vect_to_list.
Hint Rewrite @vect_to_list_const : vect_to_list.
Hint Rewrite @vect_to_list_map : vect_to_list.

Definition vect_NoDup {T n} (v: vect T n) : Prop :=
  List.NoDup (vect_to_list v).

Lemma NoDup_dec {A}:
  (forall x y:A, {x = y} + {x <> y}) ->
  forall (l: list A), {NoDup l} + {~ NoDup l}.
Proof.
  intro Hdec; induction l as [| a0 l IHl].
  - eauto using NoDup_nil.
  - destruct (in_dec Hdec a0 l), IHl;
      (eauto using NoDup_cons || (right; inversion 1; subst; contradiction)).
Defined.

Definition vect_no_dup {A n} {EQ: EqDec A} (v: vect A n) :=
  if NoDup_dec eq_dec (vect_to_list v) then true else false.

Lemma vect_NoDup_nth {T sz}:
  forall (v: vect T sz),
    vect_NoDup v <-> (forall idx idx', vect_nth v idx' = vect_nth v idx -> idx' = idx).
Proof.
  unfold vect_NoDup; split.
  - intros HNoDup **; rewrite NoDup_nth_error in HNoDup.
    apply index_to_nat_injective, HNoDup.
    rewrite vect_to_list_length; apply index_to_nat_bounded.
    rewrite !vect_to_list_nth; congruence.
  - intros Hinj. rewrite NoDup_nth_error; intros n1 n2 Hlt Heq.
    rewrite vect_to_list_length in Hlt.
    destruct (index_of_nat_bounded Hlt) as [ idx1 Heq1 ].
    apply index_to_nat_of_nat in Heq1; subst.
    rewrite vect_to_list_nth in Heq.
    assert (n2 < sz) as Hlt2 by (rewrite <- (vect_to_list_length v); apply nth_error_Some; congruence).
    destruct (index_of_nat_bounded Hlt2) as [ idx2 Heq2 ].
    apply index_to_nat_of_nat in Heq2; subst.
    rewrite vect_to_list_nth in Heq.
    inversion Heq as [Heq'].
    rewrite (Hinj _ _ Heq');
      reflexivity.
Qed.

Lemma vect_no_dup_NoDup {T sz} {EQ: EqDec T}:
  forall (v: vect T sz), vect_no_dup v = true <-> vect_NoDup v.
Proof.
  unfold vect_NoDup, vect_no_dup.
  intros; destruct NoDup_dec; intuition; discriminate.
Qed.

Lemma vect_index_nth {T sz} {EQ: EqDec T}:
  forall (v: vect T sz),
    vect_NoDup v ->
    forall (idx: index sz), vect_index (vect_nth v idx) v = Some idx.
Proof.
  intros v HNoDup idx.
  destruct (vect_index _ _) as [ idx' | ] eqn:Heq.
  - rewrite vect_NoDup_nth in HNoDup.
    f_equal; apply vect_nth_index in Heq; eauto.
  - eapply vect_nth_index_None in Heq.
    contradiction Heq; reflexivity.
Qed.

Instance EqDec_vect_nil T `{EqDec T} : EqDec (vect_nil_t T) := _.
Instance EqDec_vect_cons A B `{EqDec A} `{EqDec B} : EqDec (vect_cons_t A B) := _.
Instance EqDec_vect T n `{EqDec T} : EqDec (vect T n).
Proof. induction n; cbn; eauto using EqDec_vect_nil, EqDec_vect_cons; eassumption. Defined.

Module Bits.
  Notation bits := (vect bool).
  Notation nil := (@vect_nil bool).
  Notation cons := (@vect_cons bool).
  Notation const := (@vect_const bool).
  Notation app := (fun x y => @vect_app bool _ _ y x). (* !! *)
  Notation split := (@vect_split bool).
  Notation nth := (@vect_nth bool).
  Notation hd := (@vect_hd bool).
  Notation tl := (@vect_tl bool).
  Notation single := (@hd 0).
  Notation map := (@vect_map bool).
  Notation map2 := (@vect_map2 bool).
  Notation of_list := (@vect_of_list bool).
  Notation extend_beginning := (@vect_extend_beginning bool).
  Notation extend_end := (@vect_extend_end bool).
  Notation zeroes n := (@const n false).
  Notation ones n := (@const n true).
  Notation lsb := (@vect_hd_default bool _ false).
  Notation msb := (@vect_last_default bool _ false).

  Definition neg {sz} (b: bits sz) :=
    map negb b.

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

  Section Casts.
    Fixpoint to_N {sz: nat} (bs: bits sz) {struct sz} : N :=
      match sz return bits sz -> N with
      | O => fun _ => 0%N
      | S n => fun bs => ((if hd bs then 1 else 0) + 2 * to_N (tl bs))%N
      end bs.

    Definition to_nat {sz: nat} (bs: bits sz) : nat :=
      N.to_nat (to_N bs).

    Definition to_index {sz} sz' (bs: bits sz) : option (index sz') :=
      index_of_nat sz' (to_nat bs).

    Fixpoint to_2cZ {sz} (bs: bits sz) : Z :=
      if msb bs then
        match to_N (neg bs) with
        | N0 => -1
        | Npos x => Zneg (Pos.succ x)
        end
      else
        match to_N bs with
        | N0 => 0
        | Npos x => Zpos x
        end%Z.

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
      | N0 => zeroes sz
      | Npos p => of_positive sz p
      end.

    Definition of_nat sz (n: nat) : bits sz :=
      of_N sz (N.of_nat n).

    Definition of_2cZ sz (z: Z) : bits sz :=
      match sz with
      | 0 => zeroes 0
      | S sz =>
        match z with
        | Z0 => zeroes (S sz)
        | Zpos x => vect_snoc false (of_positive sz x)
        | Zneg x => vect_snoc true (neg (of_N sz (N.pred (Npos x))))
        end
      end.
  End Casts.

  Section Arithmetic.
    Definition zero sz : bits sz := of_N sz N.zero.
    Definition one sz : bits sz := of_N sz N.one.

    Definition plus {sz} (bs1 bs2: bits sz) :=
      Bits.of_N sz (Bits.to_N bs1 + Bits.to_N bs2)%N.

    Definition minus {sz} (bs1 bs2: bits sz) :=
      plus (plus bs1 (neg bs2)) (one sz).
  End Arithmetic.

  Section Comparisons.
    Definition lift_comparison {A sz}
               (cast: bits sz -> A) (compare: A -> A -> comparison)
               (cmp: comparison -> bool)
               (bs1 bs2: bits sz) : bool :=
      cmp (compare (cast bs1) (cast bs2)).

    Scheme Equality for comparison.
    Infix "==c" := comparison_beq (at level 0).
    Open Scope bool_scope.

    Definition is_lt (cmp: comparison) : bool :=
      cmp ==c Lt.
    Definition is_le (cmp: comparison) : bool :=
      cmp ==c Lt || cmp ==c Eq.
    Definition is_gt (cmp: comparison) : bool :=
      cmp ==c Gt.
    Definition is_ge (cmp: comparison) : bool :=
      cmp ==c Gt || cmp ==c Eq.

    Definition unsigned_lt {sz} (bs1 bs2: bits sz) : bool :=
      lift_comparison Bits.to_N N.compare is_lt bs1 bs2.
    Definition unsigned_le {sz} (bs1 bs2: bits sz) : bool :=
      lift_comparison Bits.to_N N.compare is_le bs1 bs2.
    Definition unsigned_gt {sz} (bs1 bs2: bits sz) : bool :=
      lift_comparison Bits.to_N N.compare is_gt bs1 bs2.
    Definition unsigned_ge {sz} (bs1 bs2: bits sz) : bool :=
      lift_comparison Bits.to_N N.compare is_ge bs1 bs2.

    Definition signed_lt {sz} (bs1 bs2: bits sz) : bool :=
      lift_comparison Bits.to_2cZ Z.compare is_lt bs1 bs2.
    Definition signed_le {sz} (bs1 bs2: bits sz) : bool :=
      lift_comparison Bits.to_2cZ Z.compare is_le bs1 bs2.
    Definition signed_gt {sz} (bs1 bs2: bits sz) : bool :=
      lift_comparison Bits.to_2cZ Z.compare is_gt bs1 bs2.
    Definition signed_ge {sz} (bs1 bs2: bits sz) : bool :=
      lift_comparison Bits.to_2cZ Z.compare is_ge bs1 bs2.
  End Comparisons.

  Section Properties.
    Lemma single_cons :
      forall bs, cons (single bs) nil = bs.
    Proof.
      destruct bs as [ ? [ ] ]; reflexivity.
    Qed.

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
  End Properties.
End Bits.

Declare Scope bits.
Notation bits n := (Bits.bits n).
Notation "'Ob'" := Bits.nil (at level 7) : bits.
Notation "bs '~' b" := (Bits.cons b bs) (at level 7, left associativity, format "bs '~' b") : bits.
Notation "bs '~' 0" := (Bits.cons false bs) (at level 7, left associativity, format "bs '~' 0") : bits.
Notation "bs '~' 1" := (Bits.cons true bs) (at level 7, left associativity, format "bs '~' 1") : bits.
Global Open Scope bits.

Definition pow2 n :=
  Nat.pow 2 n.

Fixpoint z_range start len :=
  match len with
  | O => List.nil
  | S len => start :: z_range (Z.succ start) len
  end.

(* Eval simpl in (List.map (fun z => Bits.of_2cZ 4 z) (range (-8) 16)). *)
