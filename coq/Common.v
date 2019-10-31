Require Import Coq.Lists.List Coq.Bool.Bool Coq.Strings.String.
Require Export Coq.omega.Omega.
Import ListNotations.
Require Export Koika.EqDec Koika.Vect Koika.FiniteType.

(* https://coq-club.inria.narkive.com/HeWqgvKm/boolean-simplification *)
Hint Rewrite
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
     negb_involutive (** negb( (negb b) -> b *)
  : bool_simpl.
Ltac bool_simpl :=
  autorewrite with bool_simpl in *.

Ltac bool_step :=
  match goal with
  | [ H: _ && _ = true |- _ ] => rewrite andb_true_iff in H
  | [ H: _ && _ = false |- _ ] => rewrite andb_false_iff in H
  | [ H: _ || _ = true |- _ ] => rewrite orb_true_iff in H
  | [ H: _ || _ = false |- _ ] => rewrite orb_false_iff in H
  | [ H: negb _ = true |- _ ] => rewrite negb_true_iff in H
  | [ H: negb _ = false |- _ ] => rewrite negb_false_iff in H
  | [ H: forallb _ (_ ++ _) = _ |- _ ] => rewrite forallb_app in H
  | [ H: Some _ = Some _ |- _ ] => inversion H; subst; clear H
  end.

Ltac cleanup_step :=
  match goal with
  | _ => discriminate
  | _ => progress (subst; cbn)
  | [ H: Some _ = Some _ |- _ ] =>
    inversion H; subst; clear H
  | [ H: (_, _) = (_, _) |- _ ] =>
    inversion H; subst; clear H
  | [ H: _ /\ _ |- _ ] =>
    destruct H
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

Ltac constr_hd c :=
      match c with
      | ?f ?x => constr_hd f
      | ?g => g
      end.

Definition and_fst {A B} := fun '(conj a _: and A B) => a.
Definition and_snd {A B} := fun '(conj _ b: and A B) => b.

Instance EqDec_FiniteType {T} {FT: FiniteType T} : EqDec T.
Proof.
  econstructor; intros.
  destruct (PeanoNat.Nat.eq_dec (finite_index t1) (finite_index t2)) as [ ? | Hneq ].
  - eauto using finite_index_injective.
  - right; intro Habs; apply (f_equal finite_index) in Habs.
    contradiction.
Qed.

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
    - intros; apply IHl1; omega.
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
End Lists.

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

Section string_of_nat.
  Lemma digit_lt_base m {n} : not (m + n < m).
  Proof.
    red; intros; eapply Le.le_Sn_n; eauto using Le.le_trans, Plus.le_plus_l.
  Qed.

  Definition string_of_base10_digit (n: {n | n < 10}) :=
    match n with
    | exist _ 0 _ => "0" | exist _ 1 _ => "1" | exist _ 2 _ => "2" | exist _ 3 _ => "3" | exist _ 4 _ => "4"
    | exist _ 5 _ => "5" | exist _ 6 _ => "6" | exist _ 7 _ => "7" | exist _ 8 _ => "8" | exist _ 9 _ => "9"
    | exist _ n pr => False_rect _ (digit_lt_base 10 pr)
    end%string.

  Fixpoint string_of_nat_rec (fuel: nat) (n: nat) :=
    match fuel with
    | O => ""%string
    | S fuel =>
      match (Compare_dec.lt_dec n 10) with
      | left pr  => string_of_base10_digit (exist _ n pr)
      | right pr => append (string_of_nat_rec fuel (PeanoNat.Nat.div n 10)) (string_of_nat_rec fuel (PeanoNat.Nat.modulo n 10))
      end
    end.

  Definition string_of_nat (n: nat) :=
    string_of_nat_rec (S n) n.
End string_of_nat.

Axiom __magic__ : forall {A}, A.

Global Set Nested Proofs Allowed.
