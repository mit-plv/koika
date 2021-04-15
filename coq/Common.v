(*! Utilities | Shared utilities !*)
Require Export Coq.micromega.Lia.
Require Export Coq.Arith.Arith.
Require Export Coq.Lists.List Coq.Bool.Bool Coq.Strings.String.
Require Export Koika.EqDec Koika.Vect Koika.FiniteType Koika.Show.

Export EqNotations.
Export ListNotations.
Global Open Scope string_scope.
Global Open Scope list_scope.

Ltac bool_step :=
  match goal with
  | [ H: _ && _ = true |- _ ] => rewrite andb_true_iff in H
  | [ H: _ && _ = false |- _ ] => rewrite andb_false_iff in H
  | [ H: _ || _ = true |- _ ] => rewrite orb_true_iff in H
  | [ H: _ || _ = false |- _ ] => rewrite orb_false_iff in H
  | [ H: negb _ = true |- _ ] => rewrite negb_true_iff in H
  | [ H: negb _ = false |- _ ] => rewrite negb_false_iff in H
  | [ H: forallb _ (_ ++ _) = _ |- _ ] => rewrite forallb_app in H
  end.

Lemma Some_inj : forall {T} (x y: T), Some x = Some y -> x = y.
Proof.
  congruence.
Qed.

Lemma pair_inj : forall {T U} (t1: T) (u1: U) (t2: T) (u2: U),
    (t1, u1) = (t2, u2) -> t1 = t2 /\ u1 = u2.
Proof.
  inversion 1. auto.
Qed.

Ltac cleanup_step :=
  match goal with
  | _ => discriminate
  | _ => progress (subst; cbn)
  | [ H: Some _ = Some _ |- _ ] =>
    apply Some_inj in H
  | [ H: (_, _) = (_, _) |- _ ] =>
    apply pair_inj in H
  | [ H: _ /\ _ |- _ ] =>
    destruct H
  end.

Ltac destruct_match :=
  match goal with
  | [ |- context[match ?x with _ => _ end] ] =>
    destruct x eqn:?
  end.

(** find the head of the given expression **)
Ltac head expr :=
  match expr with
    | ?f _ => head f
    | _ => expr
  end.

Ltac head_hnf expr := let expr' := eval hnf in expr in head expr'.

Ltac rewrite_all_hypotheses :=
  repeat match goal with
         | [ H: ?x = ?y |- _ ] => rewrite H
         end.

Ltac setoid_rewrite_all_hypotheses :=
  repeat match goal with
         | [ H: ?x = ?y |- _ ] => setoid_rewrite H
         end.

(** Fails if x is equal to v. Can work for hypotheses **)
Ltac assert_neq x v :=
  tryif (let _ := (constr:(eq_refl x : x = v)) in idtac) then fail else idtac.

(** Rewrite using setoid_rewrite the hypothesis in all
    other hypotheses, as well as in the goal. **)
Tactic Notation "setoid_rewrite_in_all" constr(Hx) :=
  repeat match goal with
         | _ =>
           progress (setoid_rewrite Hx)
         | [ H: _ |- _ ] =>
           assert_neq Hx H;
           progress (setoid_rewrite Hx in H)
         end.

Tactic Notation "setoid_rewrite_in_all" "<-" constr(Hx) :=
  repeat match goal with
         | _ =>
           progress (setoid_rewrite <-Hx)
         | [ H: _ |- _ ] =>
           assert_neq Hx H;
           progress (setoid_rewrite <-Hx in H)
         end.

Ltac set_fixes :=
  repeat match goal with
         | [  |- context[?x] ] => is_fix x; set x in *
         end.

Inductive DP {A: Type} (a: A) : Prop :=.

Inductive Posed : list Prop -> Prop :=
| AlreadyPosed1 : forall {A} a, Posed [@DP A a]
| AlreadyPosed2 : forall {A1 A2} a1 a2, Posed [@DP A1 a1; @DP A2 a2]
| AlreadyPosed3 : forall {A1 A2 A3} a1 a2 a3, Posed [@DP A1 a1; @DP A2 a2; @DP A3 a3]
| AlreadyPosed4 : forall {A1 A2 A3 A4} a1 a2 a3 a4, Posed [@DP A1 a1; @DP A2 a2; @DP A3 a3; @DP A4 a4].

Tactic Notation "_pose_once" constr(witness) constr(thm) :=
  let tw := (type of witness) in
  match goal with
  | [ H: Posed ?tw' |- _ ] =>
    unify tw (Posed tw')
  | _ => pose proof thm;
        pose proof witness
  end.

Tactic Notation "pose_once" constr(thm) :=
  progress (let witness := constr:(AlreadyPosed1 thm) in
            _pose_once witness thm).

Tactic Notation "pose_once" constr(thm) constr(arg) :=
  progress (let witness := constr:(AlreadyPosed2 thm arg) in
            _pose_once witness (thm arg)).

Tactic Notation "pose_once" constr(thm) constr(arg) constr(arg') :=
  progress (let witness := constr:(AlreadyPosed3 thm arg arg') in
            _pose_once witness (thm arg arg')).

Tactic Notation "pose_once" constr(thm) constr(arg) constr(arg') constr(arg'') :=
  progress (let witness := constr:(AlreadyPosed4 thm arg arg' arg'') in
            _pose_once witness (thm arg arg' arg'')).

Ltac remember_once x :=
  match goal with
  | [ H: ?v = x |- _ ] =>
    is_var v
  | _ =>
    let Hx := fresh "H" in
    remember x eqn:Hx;
    setoid_rewrite_in_all <- Hx
  end.

Ltac constr_hd c :=
      match c with
      | ?f ?x => constr_hd f
      | ?g => g
      end.

Definition and_fst {A B} := fun '(conj a _: and A B) => a.
Definition and_snd {A B} := fun '(conj _ b: and A B) => b.

Fixpoint upto (n: nat) :=
  match n with
  | O => [0]
  | S x => n :: upto x
  end.

Notation log2 := Nat.log2_up.

Instance EqDec_FiniteType {T} {FT: FiniteType T} : EqDec T | 3.
Proof.
  econstructor; intros.
  destruct (PeanoNat.Nat.eq_dec (finite_index t1) (finite_index t2)) as [ ? | Hneq ].
  - eauto using finite_index_injective.
  - right; intro Habs; apply (f_equal finite_index) in Habs.
    contradiction.
Defined.

Definition opt_bind {A B} (o: option A) (f: A -> option B) :=
  match o with
  | Some x => f x
  | None => None
  end.

Lemma opt_bind_f_equal {A B} o o' f f':
  o = o' ->
  (forall a, f a = f' a) ->
  @opt_bind A B o f = opt_bind o' f'.
Proof.
  intros * -> **; destruct o'; eauto.
Qed.

Notation "'let/opt' var ':=' expr 'in' body" :=
  (opt_bind expr (fun var => body)) (at level 200).

Notation "'let/opt2' v1 ',' v2 ':=' expr 'in' body" :=
  (opt_bind expr (fun '(v1, v2) => body)) (at level 200).

Notation "'let/opt3' v1 ',' v2 ',' v3 ':=' expr 'in' body" :=
  (opt_bind expr (fun '(v1, v2, v3) => body)) (at level 200).

Definition must {A} (o: option A) : if o then A else unit :=
  match o with
  | Some a => a
  | None => tt
  end.

Section Lists.
  Fixpoint list_find_opt {A B} (f: A -> option B) (l: list A) : option B :=
    match l with
    | [] => None
    | x :: l =>
      let fx := f x in
      match fx with
      | Some y => Some y
      | None => list_find_opt f l
      end
    end.

  Definition list_sum' n l :=
    List.fold_right (fun x acc => acc + x) n l.

  Definition list_sum l :=
    list_sum' 0 l.

  Lemma list_sum'_0 :
    forall l n, list_sum' n l = list_sum' 0 l + n.
  Proof.
    induction l; cbn; intros.
    - reflexivity.
    - rewrite IHl.
      rewrite !Plus.plus_assoc_reverse.
      rewrite (Plus.plus_comm n a); reflexivity.
  Qed.

  Lemma list_sum_app :
    forall l1 l2, list_sum (l1 ++ l2) = list_sum l1 + list_sum l2.
  Proof.
    unfold list_sum, list_sum'; intros.
    rewrite fold_right_app, list_sum'_0.
    reflexivity.
  Qed.

  Lemma list_sum_firstn_le :
    forall n l, list_sum (firstn n l) <= list_sum l.
  Proof.
    induction n; destruct l; cbn; auto with arith.
  Qed.

  Lemma list_sum_skipn_le :
    forall n l, list_sum (skipn n l) <= list_sum l.
  Proof.
    induction n; destruct l; cbn; auto with arith.
  Qed.

  Fixpoint skipn_firstn {A} n n' (l: list A):
    List.skipn n (List.firstn n' l) =
    List.firstn (n' - n) (List.skipn n l).
  Proof.
    destruct n, n', l; cbn; try reflexivity.
    - destruct (n' - n); reflexivity.
    - rewrite skipn_firstn; reflexivity.
  Qed.

  Fixpoint firstn_skipn {A} n n' (l: list A):
    List.firstn n (List.skipn n' l) =
    List.skipn n' (List.firstn (n' + n) l).
  Proof.
    destruct n, n', l; cbn; try reflexivity;
      rewrite <- firstn_skipn; reflexivity.
  Qed.

  Fixpoint firstn_firstn {A} n n' (l: list A):
    List.firstn n (List.firstn n' l) =
    List.firstn (Nat.min n n') l.
  Proof.
    destruct n, n', l; cbn; auto using f_equal.
  Qed.

  Lemma firstn_map {A B} (f : A -> B) :
    forall n (l: list A),
      List.firstn n (List.map f l) =
      List.map f (List.firstn n l).
  Proof.
    induction n; destruct l; subst; cbn; auto using f_equal.
  Qed.

  Lemma skipn_map {A B} (f : A -> B) :
    forall n (l: list A),
      List.skipn n (List.map f l) =
      List.map f (List.skipn n l).
  Proof.
    induction n; destruct l; subst; cbn; auto using f_equal.
  Qed.

  Lemma skipn_app {A}:
    forall (l1 l2: list A) n,
      n <= List.length l1 ->
      skipn n (List.app l1 l2) = List.app (skipn n l1) l2.
  Proof.
    induction l1; destruct n; cbn; try (inversion 1; reflexivity).
    - intros; apply IHl1; lia.
  Qed.

  Lemma forallb_pointwise {A} :
    forall f1 f2 (ls: list A),
      (forall x, List.In x ls -> f1 x = f2 x) ->
      forallb f1 ls = forallb f2 ls.
  Proof.
    induction ls; cbn.
    - reflexivity.
    - intros; f_equal; eauto.
  Qed.

  Fixpoint dedup {A} {EQ: EqDec A} (acc: list A) (l: list A) :=
    match l with
    | [] => acc
    | a :: l =>
      let already_seen := List.in_dec eq_dec a acc in
      let acc := if already_seen then acc else a :: acc in
      dedup acc l
    end.

  Fixpoint iterate_tr (n: nat) {A} (f: A -> A) (init: A) :=
    match n with
    | 0 => init
    | S n => iterate_tr n f (f init)
    end.

  Fixpoint iterate (n: nat) {A} (f: A -> A) (init: A) :=
    match n with
    | 0 => init
    | S n => f (iterate n f init)
    end.

  Lemma iterate_assoc:
    forall (n: nat) {A} (f: A -> A) (init: A),
      iterate n f (f init) = f (iterate n f init).
  Proof.
    induction n; simpl; intros; try rewrite IHn; reflexivity.
  Qed.

  Lemma iterate_S_acc :
    forall (n: nat) {A} (f: A -> A) (init: A),
      iterate (S n) f init = iterate n f (f init).
  Proof. intros; symmetry; apply iterate_assoc. Qed.

  Lemma iterate_tr_correct :
    forall (n: nat) {A} (f: A -> A) (init: A),
      iterate_tr n f init = iterate n f init.
  Proof.
    induction n; simpl; intros.
    - reflexivity.
    - rewrite IHn, iterate_assoc; reflexivity.
  Qed.

  Lemma iterate_pointwise_inv {A} (f g: A -> A) (inv: A -> Prop):
    (* Use g because that's usually the simpler one *)
    (forall x, inv x -> inv (g x)) ->
    (forall x, inv x -> f x = g x) ->
    forall n,
    forall init: A,
      inv (init) ->
      iterate n f init = iterate n g init.
  Proof.
    intros Hinv Heq; induction n; intros init Hinvi.
    - reflexivity.
    - simpl; rewrite <- !iterate_assoc, Heq; auto.
  Qed.
End Lists.

Require Lists.Streams.

Declare Scope stream_scope.
Open Scope stream_scope.

Module StreamNotations.
  Infix ":::" := Streams.Cons (at level 60, right associativity) : stream_scope.
End StreamNotations.

Module Streams.
  Include Coq.Lists.Streams.

  Import StreamNotations.

  CoFixpoint coiterate {A} (f: A -> A) (init: A) :=
    init ::: coiterate f (f init).

  Lemma coiterate_eqn {A} (f: A -> A) (init: A) :
    coiterate f init =
    init ::: coiterate f (f init).
  Proof.
    rewrite (Streams.unfold_Stream (coiterate f init)) at 1; reflexivity.
  Qed.

  Lemma map_eqn {A B} (f: A -> B) (s: Streams.Stream A) :
    Streams.map f s =
    f (Streams.hd s) ::: Streams.map f (Streams.tl s).
  Proof.
    rewrite (Streams.unfold_Stream (Streams.map f s)) at 1; reflexivity.
  Qed.

  Lemma Str_nth_0 {A} (hd: A) tl:
    Streams.Str_nth 0 (hd ::: tl) = hd.
  Proof. reflexivity. Qed.

  Lemma Str_nth_S {A} (hd: A) tl n:
    Streams.Str_nth (S n) (hd ::: tl) = Streams.Str_nth n tl.
  Proof. reflexivity. Qed.

  Lemma Str_nth_coiterate {A} (f: A -> A) :
    forall n (init: A),
      Streams.Str_nth n (coiterate f init) =
      iterate n f init.
  Proof.
    setoid_rewrite <- iterate_tr_correct.
    induction n; cbn; intros.
    - reflexivity.
    - rewrite coiterate_eqn.
      apply IHn.
  Qed.

  Lemma coiterate_pointwise {A} (f g: A -> A):
    (forall x, f x = g x) ->
    forall init: A,
      Streams.EqSt (coiterate f init) (coiterate g init).
  Proof.
    intros Heq; cofix IH; intros init.
    constructor; simpl.
    - reflexivity.
    - rewrite Heq; apply IH.
  Qed.

  Lemma coiterate_pointwise_inv {A} (f g: A -> A) (inv: A -> Prop):
    (forall x, inv x -> inv (g x)) -> (* Use g because that's usually the simpler one *)
    (forall x, inv x -> f x = g x) ->
    forall init: A,
      inv (init) ->
      Streams.EqSt (coiterate f init) (coiterate g init).
  Proof.
    intros Hinv Heq; cofix IH; intros init Hinvi.
    constructor; simpl.
    - reflexivity.
    - rewrite Heq; auto.
  Qed.

  Fixpoint firstn {A} (n: nat) (s: Stream A) : list A :=
    match n with
    | 0 => []
    | S n => match s with
            | Cons hd tl => hd :: firstn n tl
            end
    end.
End Streams.

Inductive result {S F} :=
| Success (s: S)
| Failure (f: F).

Arguments result : clear implicits.

Definition result_map_failure {S F1 F2} (fn: F1 -> F2) (r: result S F1) :=
  match r with
  | Success s => Success s
  | Failure f => Failure (fn f)
  end.

Definition opt_result {S F} (o: option S) (f: F): result S F :=
  match o with
  | Some x => Success x
  | None => Failure f
  end.

Notation "'let/res' var ':=' expr 'in' body" :=
  (match expr with
   | Success var => body
   | Failure f => Failure f
   end)
    (at level 200).

Section result_list_map.
  Context {A B F: Type}.
  Context (f: A -> result B F).

  (* Written this way to allow use in fixpoints *)
  Fixpoint result_list_map (la: list A): result (list B) F :=
    match la with
    | [] => Success []
    | a :: la => let/res b := f a in
               let/res la := result_list_map la in
               Success (b :: la)
    end.
End result_list_map.

Definition is_success {S F} (r: result S F) :=
  match r with
  | Success s => true
  | Failure f => false
  end.

Definition extract_success {S F} (r: result S F) (pr: is_success r = true) :=
  match r return is_success r = true -> S with
  | Success s => fun _ => s
  | Failure f => fun pr => match Bool.diff_false_true pr with end
  end pr.

Global Set Nested Proofs Allowed.
