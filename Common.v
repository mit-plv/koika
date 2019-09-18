Require Import Coq.Lists.List Coq.Bool.Bool Coq.Strings.String.
Import ListNotations.
Require Export SGA.EqDec SGA.Vect SGA.FiniteType.

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

Definition must {A} (o: option A) : if o then A else unit :=
  match o with
  | Some a => a
  | None => tt
  end.

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
