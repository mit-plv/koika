(*! Utilities | Vectors and bitvector library !*)
Require Import Coq.Lists.List Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.Arith.
Require Export Coq.NArith.NArith.          (* Coq bug: If this isn't exported, other files can't import Vect.vo *)
Require Import Coq.ZArith.ZArith.
Require Import Koika.EqDec.
Import EqNotations.

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
  rew eq in idx.

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

Lemma index_of_nat_none_ge :
  forall sz n,
    index_of_nat sz n = None ->
    n >= sz.
Proof.
  intros; destruct (ge_dec n sz) as [ ? | Hle ].
  - eassumption.
  - apply not_ge, index_of_nat_bounded in Hle; destruct Hle;
      congruence.
Qed.

Lemma index_of_nat_ge_none :
  forall sz n,
    n >= sz ->
    index_of_nat sz n = None.
Proof.
  induction sz; cbn; intros.
  - reflexivity.
  - destruct n.
    + lia.
    + rewrite IHsz by lia; reflexivity.
Qed.

Definition index_of_nat_lt (sz n: nat)
  : n < sz -> index sz.
Proof.
  destruct (index_of_nat sz n) as [idx | ] eqn:Heq; intros Hlt.
  - exact idx.
  - exfalso; apply index_of_nat_none_ge in Heq; lia.
Defined.

Fixpoint largest_index sz : index (S sz) :=
  match sz with
  | 0 => thisone
  | S sz => anotherone (largest_index sz)
  end.

Lemma index_of_nat_largest sz :
  index_of_nat (S sz) sz = Some (largest_index sz).
Proof.
  induction sz; cbn.
  - reflexivity.
  - destruct sz; cbn in *.
    + reflexivity.
    + rewrite IHsz.
      reflexivity.
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

Fixpoint vect_app {T} {sz1 sz2} (v1: vect T sz1) (v2: vect T sz2) {struct sz1} : vect T (sz1 + sz2) :=
  match sz1 as n return (vect T n -> vect T (n + sz2)) with
  | 0 => fun _ => v2
  | S sz1 => fun v1 => vect_cons (vect_hd v1) (vect_app (vect_tl v1) v2)
  end v1.

Fixpoint vect_app_nil_cast n:
  n = n + 0.
Proof. destruct n; cbn; auto. Defined.

Lemma vect_app_nil :
  forall {T sz} (v: vect T sz) (v0: vect T 0),
    vect_app v v0 =
    rew (vect_app_nil_cast _) in v.
Proof.
  destruct v0.
  induction sz; destruct v; cbn.
  - reflexivity.
  - rewrite IHsz.
    unfold f_equal_nat, f_equal.
    rewrite <- vect_app_nil_cast; reflexivity.
Defined.

Lemma vect_app_cast_l {T} {sz1 sz1' sz2}:
  forall (h: sz1 = sz1') (v1: vect T sz1) (v2: vect T sz2),
    vect_app (rew h in v1) v2 = rew [fun sz => vect T (sz + sz2)] h in (vect_app v1 v2).
Proof. destruct h; reflexivity. Defined.

Lemma vect_app_cast_r {T} {sz1 sz1' sz2}:
  forall (h: sz1 = sz1') (v1: vect T sz1) (v2: vect T sz2),
    vect_app v2 (rew h in v1) = rew [fun sz => vect T (sz2 + sz)] h in (vect_app v2 v1).
Proof. destruct h; reflexivity. Defined.

Fixpoint vect_repeat {T} {sz} (n: nat) (v: vect T sz) : vect T (n * sz) :=
  match n with
  | 0 => vect_nil
  | S n => vect_app v (vect_repeat n v)
  end.

Lemma vect_repeat_single_const {T} n :
  forall (t: T), vect_repeat n (vect_cons t vect_nil) = vect_const (n * 1) t.
Proof.
  induction n; simpl; intros; try rewrite IHn; reflexivity.
Qed.

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

Fixpoint vect_nth_const {T} (n: nat) (t: T) idx {struct n} :
  vect_nth (vect_const n t) idx = t.
Proof.
  destruct n; cbn; destruct idx; eauto.
Defined.

Fixpoint vect_replace {T n} (v: vect T n) (idx: index n) (t: T) :=
  match n return (vect T n -> index n -> vect T n) with
  | 0 => fun _ idx => False_rect _ idx
  | S n => fun v idx =>
            match idx with
            | thisone => vect_cons t (vect_tl v)
            | anotherone idx => vect_cons (vect_hd v) (vect_replace (vect_tl v) idx t)
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

Lemma vect_last_nth {T sz} :
  forall (v: vect T (S sz)),
    vect_last v = vect_nth v (largest_index sz).
Proof.
  induction sz; simpl; intros; try rewrite IHsz; reflexivity.
Qed.

Fixpoint vect_map {T T' n} (f: T -> T') (v: vect T n) : vect T' n :=
  match n return vect T n -> vect T' n with
  | O => fun _ => vect_nil
  | S _ => fun v => vect_cons (f (vect_hd v)) (vect_map f (vect_tl v))
  end v.

Fixpoint vect_nth_map {T T' sz} (f: T -> T') {struct sz}:
  forall (v: vect T sz) idx,
    vect_nth (vect_map f v) idx = f (vect_nth v idx).
Proof.
  destruct sz, idx; cbn; eauto.
Defined.

Lemma vect_map_map {T T' T'' n} (f: T -> T') (f': T' -> T'') :
  forall (v: vect T n),
    vect_map f' (vect_map f v) = vect_map (fun x => f' (f x)) v.
Proof.
  induction n; cbn; intros; rewrite ?IHn; reflexivity.
Qed.

Lemma vect_map_pointwise_morphism {T T' n} (f f': T -> T') :
  (forall x, f x = f' x) ->
  forall (v: vect T n), vect_map f v = vect_map f' v.
Proof.
  induction n; cbn; intros; rewrite ?H, ?IHn by eassumption; reflexivity.
Qed.

Lemma vect_map_id {T n} (f: T -> T):
  (forall x, f x = x) ->
  forall (v: vect T n), vect_map f v = v.
Proof.
  induction n; destruct v; cbn; intros; rewrite ?H, ?IHn by eassumption; reflexivity.
Qed.

Fixpoint vect_map2 {T1 T2 T n} (f: T1 -> T2 -> T) (v1: vect T1 n) (v2: vect T2 n) : vect T n :=
  match n return vect T1 n -> vect T2 n -> vect T n with
  | O => fun _ _ => vect_nil
  | S _ => fun v1 v2 => vect_cons (f (vect_hd v1) (vect_hd v2))
                              (vect_map2 f (vect_tl v1) (vect_tl v2))
  end v1 v2.

Fixpoint vect_nth_map2 {T1 T2 T n} (f: T1 -> T2 -> T) (v1: vect T1 n) (v2: vect T2 n) {struct n}:
  forall idx, vect_nth (vect_map2 f v1 v2) idx = f (vect_nth v1 idx) (vect_nth v2 idx).
Proof.
  destruct n, idx; cbn; eauto.
Defined.

Definition vect_zip {T1 T2 n} (v1: vect T1 n) (v2: vect T2 n) : vect (T1 * T2) n :=
  vect_map2 (fun b1 b2 => (b1, b2)) v1 v2.

Definition vect_nth_zip {T1 T2 n} (v1: vect T1 n) (v2: vect T2 n) :
  forall idx, vect_nth (vect_zip v1 v2) idx = (vect_nth v1 idx, vect_nth v2 idx).
Proof.
  apply vect_nth_map2.
Defined.

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

Fixpoint vect_dotimes {A} (f: A -> A) n (v: A)
  : A :=
  match n with
  | O => v
  | S n => vect_dotimes f n (f v)
  end.

Definition vect_cycle_l {T sz} n (v: vect T sz) :=
  vect_dotimes vect_cycle_l1 n v.

Definition vect_cycle_r {T sz} n (v: vect T sz) :=
  vect_dotimes vect_cycle_r1 n v.

Fixpoint vect_skipn_cast n:
  n = n - 0.
Proof. destruct n; cbn; auto. Defined.

Fixpoint vect_skipn {T sz} (n: nat) (v: vect T sz) : vect T (sz - n) :=
  match n with
  | 0 => rew (vect_skipn_cast sz) in v
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
    rew <- (vect_firstn_id_cast sz) in v.
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
  rew (vect_firstn_plus_cast sz n) in
    (vect_firstn n v).

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
  rew (vect_skipn_plus_cast sz n) in
    (vect_skipn n v).

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
    rew <- (vect_skipn_plus_cast sz n) in (vect_skipn_plus n v).
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
Proof. destruct x; cbn; rewrite ?vect_extend_beginning_cast'; reflexivity. Defined.

Fixpoint vect_extend_beginning_cast sz sz':
  sz' - sz + sz = Nat.max sz sz'.
Proof.
  destruct sz, sz'; cbn; auto.
  cbn; rewrite <- vect_extend_beginning_cast; apply vect_extend_beginning_cast'.
Defined.

Definition vect_extend_beginning {T sz} (v: vect T sz) (sz': nat) (t: T) : vect T (Nat.max sz sz') :=
  rew (vect_extend_beginning_cast sz sz') in
    (vect_app (vect_const (sz' - sz) t) v).

Fixpoint vect_extend_end_cast sz sz':
  sz + (sz' - sz) = Nat.max sz sz'.
Proof. destruct sz, sz'; cbn; auto. Defined.

Definition vect_extend_end {T sz} (v: vect T sz) (sz': nat) (t: T) : vect T (Nat.max sz sz') :=
  rew (vect_extend_end_cast sz sz') in
    (vect_app v (vect_const (sz' - sz) t)).

Fixpoint vect_extend_end_firstn_cast sz sz':
  Nat.max (Nat.min sz sz') sz = sz.
Proof. destruct sz, sz'; cbn; auto. Defined.

Definition vect_extend_end_firstn {T sz sz'} (v: vect T (Nat.min sz sz')) (t: T) : vect T sz :=
  rew (vect_extend_end_firstn_cast sz sz') in
    (vect_extend_end v sz t).

Lemma vect_extend_end_firstn_simpl :
  forall {T sz} (v: vect T sz) n b,
  forall (eqn: Nat.min n sz = n),
    vect_extend_end_firstn (vect_firstn n v) b =
    rew eqn in (vect_firstn n v).
Proof.
  unfold vect_extend_end_firstn, vect_extend_end; intros.
  rewrite <- eq_trans_rew_distr.
  set (eq_trans _ _) as Heq; clearbody Heq.
  revert Heq; replace (n - Nat.min n sz) with 0 by lia; intros.
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

  Fixpoint vect_to_list_nth {T sz} {struct sz}:
    forall (v: vect T sz) idx,
      List.nth_error (vect_to_list v) (index_to_nat idx) =
      Some (vect_nth v idx).
  Proof.
    destruct sz, v, idx; cbn.
    - reflexivity.
    - apply vect_to_list_nth.
  Defined.

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

  Lemma vect_to_list_eq_rect_fn {T sz sz'} (f: nat -> nat):
    forall (v: vect T (f sz)) (pr: sz = sz'),
      vect_to_list (rew [fun sz => vect T (f sz)] pr in v) = vect_to_list v.
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
Hint Rewrite @vect_to_list_eq_rect_fn : vect_to_list.
Hint Rewrite @vect_to_list_app : vect_to_list.
Hint Rewrite @vect_to_list_firstn : vect_to_list.
Hint Rewrite @vect_to_list_skipn : vect_to_list.
Hint Rewrite @vect_to_list_const : vect_to_list.
Hint Rewrite @vect_to_list_map : vect_to_list.
Hint Rewrite @vect_to_list_length : vect_to_list.

Hint Rewrite @firstn_firstn : vect_to_list_cleanup.
Hint Rewrite @List.firstn_app : vect_to_list_cleanup.
Hint Rewrite @List.skipn_app : vect_to_list.
Hint Rewrite @List.firstn_nil : vect_to_list_cleanup.
Hint Rewrite @List.firstn_length : vect_to_list_cleanup.
Hint Rewrite @Nat.sub_0_r : vect_to_list_cleanup.
Hint Rewrite @List.app_nil_r : vect_to_list_cleanup.
Hint Rewrite @Nat.sub_diag : vect_to_list_cleanup.

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

Require Import Lia.

Section Npow2.
  Open Scope N_scope.

  Lemma Npow2_ge_1 :
    forall n, (1 <= N.pow 2 n)%N.
  Proof.
    induction n using N.peano_ind.
    - reflexivity.
    - rewrite N.pow_succ_r'; nia.
  Qed.

  Lemma N_lt_pow2_succ_1 :
    forall n m,
      1 + 2 * n < 2 ^ N.succ m ->
      n < 2 ^ m.
  Proof.
    intros * Hlt.
    rewrite N.pow_succ_r' in Hlt.
    rewrite N.mul_lt_mono_pos_l with (p := 2).
    rewrite N.add_1_l in Hlt.
    apply N.lt_succ_l.
    eassumption.
    econstructor.
  Qed.

  Lemma N_lt_pow2_succ :
    forall n m,
      2 * n < 2 ^ N.succ m ->
      n < 2 ^ m.
  Proof.
    intros * Hlt.
    rewrite N.pow_succ_r' in Hlt.
    rewrite N.mul_lt_mono_pos_l with (p := 2).
    eassumption.
    econstructor.
  Qed.
End Npow2.

Section pow2.
  (* The S (pred …) makes it clear to the typechecher that the result is nonzero *)
  Definition pow2 n :=
    S (pred (Nat.pow 2 n)).

  Arguments pow2 / !n : assert.

  Lemma pow2_correct : forall n, pow2 n = Nat.pow 2 n.
  Proof.
    unfold pow2; induction n; simpl.
    - reflexivity.
    - destruct (Nat.pow 2 n); simpl; (discriminate || reflexivity).
  Qed.

  Lemma le_pow2_log2 :
    forall sz, sz <= pow2 (Nat.log2_up sz).
  Proof.
    intros; rewrite pow2_correct.
    destruct sz; [ | apply Nat.log2_log2_up_spec ]; auto with arith.
  Qed.

  Lemma pred_lt_pow2_log2 :
    forall sz, pred sz < pow2 (Nat.log2_up sz).
  Proof.
    destruct sz; cbn; auto using le_pow2_log2 with arith.
  Qed.

  Lemma N_pow_Nat_pow :
    forall n m,
      N.pow (N.of_nat m) (N.of_nat n) =
      N.of_nat (Nat.pow m n).
  Proof.
    induction n; intros.
    - reflexivity.
    - rewrite Nat2N.inj_succ; cbn; rewrite Nat2N.inj_mul, <- IHn.
      rewrite N.pow_succ_r'; reflexivity.
  Qed.
End pow2.

Module VectNotations.
  Declare Scope vect.
  Delimit Scope vect with vect.
  Notation "[ ]" := (vect_nil) (format "[ ]") : vect.
  Notation "h :: t" := (vect_cons h t) (at level 60, right associativity) : vect.
  Notation "[ x ]" := (vect_cons x vect_nil) : vect.
  Notation "[ x ; y ; .. ; z ]" := (vect_cons x (vect_cons y .. (vect_cons z vect_nil) ..)) : vect.
  Infix "++" := vect_app : vect.
End VectNotations.

Export VectNotations.

(* https://coq-club.inria.narkive.com/HeWqgvKm/boolean-simplification *)
Hint Rewrite
     andb_diag (** b && b -> b **)
     orb_diag (** b || b -> b **)
     orb_false_r (** b || false -> b *)
     orb_false_l (** false || b -> b *)
     orb_true_r (** b || true -> true *)
     orb_true_l (** true || b -> true *)
     andb_false_r (** b && false -> false *)
     andb_false_l (** false && b -> false *)
     andb_true_r (** b && true -> b *)
     andb_true_l (** true && b -> b *)
     negb_orb (** negb (b || c) -> negb b && negb c *)
     negb_andb (** negb (b && c) -> negb b || negb c *)
     negb_involutive (** negb (negb b) -> b *)
  : bool_simpl.
Ltac bool_simpl :=
  autorewrite with bool_simpl in *.

Module Bits.
  Notation bits := (vect bool).
  Notation nil := (@vect_nil bool).
  Notation cons := (@vect_cons bool).
  Notation const := (@vect_const bool).
  Notation app := (fun x y => @vect_app bool _ _ y x). (* !! *)
  Notation repeat := (@vect_repeat bool).
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

  Fixpoint rmul n m :=
    match n with
    | 0 => 0
    | S p => rmul p m + m
    end.

  Lemma rmul_correct : forall n m, rmul n m = Nat.mul n m.
  Proof. induction n; cbn; intros; rewrite ?IHn; auto with arith. Qed.

  Fixpoint splitn {n sz} (bs: bits (rmul n sz)) : vect (bits sz) n :=
    match n return bits (rmul n sz) -> vect (bits sz) n with
    | 0 => fun _ => vect_nil
    | S n => fun v => let (rest, hd) := vect_split v in
                  vect_cons hd (splitn rest)
    end bs.

  Fixpoint appn {n sz} (bss: vect (bits sz) n) : bits (rmul n sz) :=
    match n return vect (bits sz) n -> bits (rmul n sz) with
    | 0 => fun _ => Bits.nil
    | S n => fun v => Bits.app (vect_hd v) (appn (vect_tl v))
    end bss.

  Lemma splitn_appn {n sz} :
    forall (bss: vect (bits sz) n), splitn (appn bss) = bss.
  Proof.
    induction n; cbn; intros.
    - destruct bss; reflexivity.
    - rewrite vect_split_app, IHn.
      reflexivity.
  Qed.

  Lemma appn_splitn {n sz} :
    forall (bs: bits (rmul n sz)), appn (splitn bs) = bs.
  Proof.
    induction n; cbn; intros.
    - destruct bs; reflexivity.
    - destruct (split _) eqn:Hsplit; cbn.
      rewrite <- (vect_app_split bs).
      set (split _) in *; rewrite Hsplit; cbn.
      rewrite IHn; reflexivity.
  Qed.

  Definition neg {sz} (b: bits sz) :=
    map negb b.

  Definition and {sz} (b1: bits sz) (b2: bits sz) :=
    map2 andb b1 b2.
  Definition or {sz} (b1: bits sz) (b2: bits sz) :=
    map2 orb b1 b2.
  Definition xor {sz} (b1: bits sz) (b2: bits sz) :=
    map2 xorb b1 b2.

  Definition asr1 {sz} (b: bits sz) :=
    match sz return bits sz -> bits sz with
    | 0 => fun b => b
    | S _ => fun b => vect_snoc (msb b) (vect_tl b)
    end b.
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

  Definition asr {sz} nplaces (b: bits sz) :=
    vect_dotimes asr1 nplaces b.
  Definition lsr {sz} nplaces (b: bits sz) :=
    vect_dotimes lsr1 nplaces b.
  Definition lsl {sz} nplaces (b: bits sz) :=
    vect_dotimes lsl1 nplaces b.

  Section Casts.
    Fixpoint to_N {sz: nat} (bs: bits sz) {struct sz} : N :=
      match sz return bits sz -> N with
      | O => fun _ => 0%N
      | S n => fun bs => ((if hd bs then 1 else 0) + 2 * to_N (tl bs))%N
      end bs.

    Global Arguments to_N sz / !bs.

    Definition to_nat {sz: nat} (bs: bits sz) : nat :=
      N.to_nat (to_N bs).

    Definition to_index {sz} sz' (bs: bits sz) : option (index sz') :=
      index_of_nat sz' (to_nat bs).

    Definition to_2cZ {sz} (bs: bits sz) : Z :=
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

    Definition of_index sz {n} (idx: index n) : bits sz :=
      of_nat sz (index_to_nat idx).

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

    Lemma to_N_rew :
      forall {sz sz'} (bs: bits sz) (eqn: sz = sz'),
        to_N (rew eqn in bs) = to_N bs.
    Proof. destruct eqn; reflexivity. Qed.

    Lemma to_N_zeroes :
      forall sz, to_N (zeroes sz) = 0%N.
    Proof. induction sz; simpl; try rewrite IHsz; reflexivity. Qed.

    Lemma to_N_app :
      forall {sz sz'} (bs: bits sz) (bs': bits sz'),
        to_N (app bs bs') = (to_N bs * 2 ^ (N.of_nat sz') + to_N bs')%N.
    Proof.
      induction sz'; destruct bs'.
      - cbn; rewrite N.mul_1_r, N.add_0_r; reflexivity.
      - rewrite Nat2N.inj_succ, N.pow_succ_r'; cbn -[N.mul].
        rewrite IHsz'; lia.
    Qed.

    Lemma to_N_of_N :
      forall n sz,
        (n < N.pow 2 (N.of_nat sz))%N ->
        to_N (of_N sz n) = n.
    Proof.
      destruct n; simpl.
      - intros; apply to_N_zeroes.
      - induction p; intros sz Hlt;
          destruct sz; try solve [inversion Hlt];
            cbn -[N.mul N.add];
            rewrite Nat2N.inj_succ in Hlt.
        1, 2: solve [intros; rewrite IHp; eauto using N_lt_pow2_succ_1, N_lt_pow2_succ].
        rewrite to_N_zeroes; reflexivity.
    Qed.

    Lemma of_N_inj :
      forall sz n1 n2,
        (n1 < N.pow 2 (N.of_nat sz))%N ->
        (n2 < N.pow 2 (N.of_nat sz))%N ->
        of_N sz n1 = of_N sz n2 ->
        n1 = n2.
    Proof.
      intros * Hlt1 Hlt2 Heq%(f_equal to_N).
      rewrite !to_N_of_N in Heq by assumption.
      assumption.
    Qed.

    Lemma to_N_inj :
      forall sz (bs1 bs2: bits sz),
        to_N bs1 = to_N bs2 ->
        bs1 = bs2.
    Proof.
      induction sz; destruct bs1, bs2; cbn; intros.
      - reflexivity.
      - destruct vhd0, vhd1, (to_N vtl0) eqn:?, (to_N vtl1) eqn:?; cbn in *;
          discriminate || (rewrite (IHsz vtl0 vtl1) by congruence; reflexivity).
    Qed.

    Lemma to_N_inj_contra :
      forall sz (bs1 bs2: bits sz),
        bs1 <> bs2 ->
        to_N bs1 <> to_N bs2.
    Proof.
      auto using to_N_inj.
    Qed.

    Lemma to_N_bounded:
      forall sz (bs: bits sz),
        (to_N bs < 2 ^ N.of_nat sz)%N.
    Proof.
      induction sz; destruct bs; cbn -[N.pow N.mul]; intros.
      - repeat econstructor.
      - setoid_rewrite Nat2N.inj_succ; rewrite N.pow_succ_r'.
        destruct vhd0, (to_N vtl0) eqn:Heq; cbn -[N.pow N.mul N.add];
          specialize (IHsz vtl0); rewrite Heq in IHsz; nia.
    Qed.

    Lemma of_N_to_N :
      forall sz (bs: bits sz),
        of_N sz (to_N bs) = bs.
    Proof.
      auto using to_N_inj, to_N_of_N, to_N_bounded.
    Qed.

    Lemma nat_lt_pow2_N (sz n: nat):
      n < pow2 sz ->
      (N.of_nat n < 2 ^ N.of_nat sz)%N.
    Proof.
      intros H.
      change 2%N with (N.of_nat 2).
      rewrite N_pow_Nat_pow.
      unfold N.lt. rewrite <- Nat2N.inj_compare, <- nat_compare_lt.
      rewrite pow2_correct in H; eassumption.
    Qed.

    Lemma to_nat_rew :
      forall {sz sz'} (bs: bits sz) (eqn: sz = sz'),
        to_nat (rew eqn in bs) = to_nat bs.
    Proof. destruct eqn; reflexivity. Qed.

    Lemma to_nat_of_nat :
      forall sz n,
        n < pow2 sz ->
        to_nat (of_nat sz n) = n.
    Proof.
      unfold to_nat, of_nat;
        intros; rewrite to_N_of_N, Nat2N.id;
          eauto using nat_lt_pow2_N.
    Qed.

    Lemma to_nat_bounded {sz} :
      forall (bs: bits sz), to_nat bs < pow2 sz.
    Proof.
      unfold to_nat; intros.
      rewrite pow2_correct, <- Nat.compare_lt_iff.
      rewrite Nat2N.inj_compare, N2Nat.id, <- N_pow_Nat_pow, N.compare_lt_iff.
      apply to_N_bounded.
    Qed.

    Definition to_index_safe {sz} (bs: bits sz) :=
      index_of_nat_lt (pow2 sz) (to_nat bs) (to_nat_bounded _).
  End Casts.

  Section Arithmetic.
    Definition zero {sz} : bits sz := of_N sz N.zero.
    Definition one {sz} : bits sz := of_N sz N.one.

    Definition plus {sz} (bs1 bs2: bits sz) :=
      Bits.of_N sz (Bits.to_N bs1 + Bits.to_N bs2)%N.

    Definition minus {sz} (bs1 bs2: bits sz) :=
      plus (plus bs1 (neg bs2)) (@one sz).

    Definition mul {sz1 sz2} (bs1: bits sz1) (bs2: bits sz2) :=
      Bits.of_N (sz1 + sz2) (Bits.to_N bs1 * Bits.to_N bs2)%N.
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

  Section Slices.
    Definition slice {sz} (offset: nat) (width: nat) (bs: bits sz) : bits width :=
      vect_extend_end_firstn (vect_firstn width (vect_skipn offset bs)) false.

    Lemma slice_subst_cast :
      forall sz width offset,
        Nat.min sz (Nat.min offset sz + (width + (sz - (offset + width)))) = sz.
    Proof.
      induction sz, width, offset; cbn; auto using Min.min_idempotent.
      - f_equal; apply (IHsz 0 offset).
      - f_equal; apply (IHsz width 0).
      - f_equal; apply (IHsz (S width) offset).
    Defined.

    Definition slice_subst {sz}
               (offset: nat)
               (width: nat)
               (bs: bits sz)
               (v: bits width) : bits sz :=
      let head := vect_firstn offset bs in
      let tail := vect_skipn (offset + width) bs in
      rew (slice_subst_cast sz width offset) in
          (vect_firstn sz (vect_app head (vect_app v tail))).
  End Slices.

  Section Properties.
    Lemma single_cons :
      forall bs, cons (single bs) nil = bs.
    Proof.
      destruct bs as [ ? [ ] ]; reflexivity.
    Qed.

    Lemma single_to_bits :
      forall bs b,
        single bs = b ->
        bs = cons b nil.
    Proof.
      intros.
      rewrite <-(single_cons bs).
      congruence.
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

  Section Binops.
    Ltac t_map sz bs :=
      destruct sz, bs; cbn; bool_simpl; try apply f_equal; auto.

    Fixpoint and_diag {sz} (bs: bits sz) {struct sz}:
      Bits.and bs bs = bs.
    Proof. unfold and in *; t_map sz bs. Defined.

    Fixpoint or_diag {sz} (bs: bits sz) {struct sz}:
      Bits.or bs bs = bs.
    Proof. unfold or in *; t_map sz bs. Defined.

    Fixpoint and_zeroes_l {sz} (bs: bits sz) {struct sz}:
      Bits.and (Bits.zeroes _) bs = Bits.zeroes _.
    Proof. unfold and in *; t_map sz bs. Defined.

    Fixpoint and_zeroes_r {sz} (bs: bits sz) {struct sz}:
      Bits.and bs (Bits.zeroes _) = Bits.zeroes _.
    Proof. unfold and in *; t_map sz bs. Defined.

    Fixpoint and_ones_l {sz} (bs: bits sz) {struct sz}:
      Bits.and (Bits.ones _) bs = bs.
    Proof. unfold and in *; t_map sz bs. Defined.

    Fixpoint and_ones_r {sz} (bs: bits sz) {struct sz}:
      Bits.and bs (Bits.ones _) = bs.
    Proof. unfold and in *; t_map sz bs. Defined.

    Fixpoint or_zeroes_l {sz} (bs: bits sz) {struct sz}:
      Bits.or (Bits.zeroes _) bs = bs.
    Proof. unfold or in *; t_map sz bs. Defined.

    Fixpoint or_zeroes_r {sz} (bs: bits sz) {struct sz}:
      Bits.or bs (Bits.zeroes _) = bs.
    Proof. unfold or in *; t_map sz bs. Defined.

    Fixpoint or_ones_l {sz} (bs: bits sz) {struct sz}:
      Bits.or (Bits.ones _) bs = Bits.ones _.
    Proof. unfold or in *; t_map sz bs. Defined.

    Fixpoint or_ones_r {sz} (bs: bits sz) {struct sz}:
      Bits.or bs (Bits.ones _) = Bits.ones _.
    Proof. unfold or in *; t_map sz bs. Defined.

    Fixpoint neg_involutive {sz} (bs: bits sz) {struct sz}:
      Bits.neg (Bits.neg bs) = bs.
    Proof. unfold neg in *; t_map sz bs. Defined.
  End Binops.
End Bits.

Hint Rewrite
     @Bits.and_diag
     @Bits.or_diag
     @Bits.or_zeroes_r
     @Bits.or_zeroes_l
     @Bits.or_ones_r
     @Bits.or_ones_l
     @Bits.and_zeroes_r
     @Bits.and_zeroes_l
     @Bits.and_ones_r
     @Bits.and_ones_l
  : bool_simpl.

Declare Scope bits.

Notation bits n := (Bits.bits n).
Notation "bs '~' b" := (Bits.cons b bs) (at level 7, left associativity, format "bs '~' b") : bits.
Notation "bs '~' 0" := (Bits.cons false bs) (at level 7, left associativity, format "bs '~' 0") : bits.
Notation "bs '~' 1" := (Bits.cons true bs) (at level 7, left associativity, format "bs '~' 1") : bits.
Notation "'Ob'" := Bits.nil (at level 7) : bits. (* https://github.com/coq/coq/issues/12370 *)

Infix "+b" := Bits.plus (at level 50, left associativity): bits.
Infix "-b" := Bits.minus (at level 50, left associativity): bits .
Infix "*b" := Bits.mul (at level 40, left associativity): bits .
Infix ">>b" := Bits.lsr (at level 30, no associativity): bits .
Infix ">>>b" := Bits.asr (at level 30, no associativity): bits .
Infix "<<b" := Bits.lsl (at level 30, no associativity): bits .
Infix "<?b" := Bits.unsigned_lt (at level 70, no associativity): bits.
Infix "<=?b" := Bits.unsigned_le (at level 70, no associativity): bits.
Infix ">?b" := Bits.unsigned_gt (at level 70, no associativity): bits.
Infix ">=?b" := Bits.unsigned_ge (at level 70, no associativity): bits.
Infix "<?sb" := Bits.signed_lt (at level 70, no associativity): bits.
Infix "<=?sb" := Bits.signed_le (at level 70, no associativity): bits.
Infix ">?sb" := Bits.signed_gt (at level 70, no associativity): bits.
Infix ">=?sb" := Bits.signed_ge (at level 70, no associativity): bits.

Global Open Scope bits.

Fixpoint z_range start len :=
  match len with
  | O => List.nil
  | S len => start :: z_range (Z.succ start) len
  end.

(* Eval simpl in (List.map (fun z => Bits.of_2cZ 4 z) (z_range (-8) 16)). *)
