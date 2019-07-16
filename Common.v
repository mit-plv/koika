Require Import Coq.Lists.List.
Import ListNotations.
Require Export SGA.Vect.

Inductive DP {A: Type} (a: A) : Prop :=.

Ltac bool_step :=
  match goal with
  | [ H: andb _ _ = true |- _ ] =>
    apply andb_prop in H
  | [ H: forallb _ (_ ++ _) = _ |- _ ] =>
    rewrite forallb_app in H
  | [ H: Some _ = Some _ |- _ ] =>
    inversion H; subst; clear H
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

Class EqDec (T: Type) :=
  { eq_dec: forall t1 t2: T, { t1 = t2 } + { t1 <> t2 } }.

Require Import String.

Hint Extern 1 (EqDec _) => econstructor; decide equality : typeclass_instances.
Hint Extern 1 ({ _ = _ } + { _ <> _ }) => apply eq_dec : typeclass_instances.

Instance EqDec_bool : EqDec bool := _.
Instance EqDec_ascii : EqDec Ascii.ascii := _.
Instance EqDec_string : EqDec string := _.
Instance EqDec_unit : EqDec unit := _.
Instance EqDec_pair A B `{EqDec A} `{EqDec B} : EqDec (A * B) := _.
Instance EqDec_option A `{EqDec A} : EqDec (option A) := _.

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
