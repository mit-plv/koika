Require Import Coq.Lists.List.
Import ListNotations.

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

Notation "'let/opt' var ':=' expr 'in' body" :=
  (opt_bind expr (fun var => body)) (at level 200).

Notation "'let/opt2' v1 ',' v2 ':=' expr 'in' body" :=
  (opt_bind expr (fun '(v1, v2) => body)) (at level 200).

Definition must {A} (o: option A) : if o then A else unit :=
  match o with
  | Some a => a
  | None => tt
  end.

Section Vect.
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
End Vect.

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
