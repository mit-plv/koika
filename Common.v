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

Section fold_left2.
  Context {A B B': Type} (f: A -> B -> B' -> A).

  Fixpoint fold_left2 (l: list B) (l': list B') (a0: A) {struct l} : A :=
    match l, l' with
    | _, nil | nil, _ => a0
    | b :: t, b' :: t' => fold_left2 t t' (f a0 b b')
    end.
End fold_left2.

Section fold_right2.
  Context {A B B': Type} (f: B -> B' -> A -> A).

  Fixpoint fold_right2 (a0: A) (l: list B) (l': list B') {struct l} : A :=
    match l, l' with
    | _, nil | nil, _ => a0
    | b :: t, b' :: t' => f b b' (fold_right2 a0 t t')
    end.
End fold_right2.

Lemma fold_right2_app {A B B'}:
  forall (f: B -> B' -> A -> A) a0 l l0 l' l'0,
    length l = length l' ->
    fold_right2 f a0 (l ++ l0) (l' ++ l'0) =
    fold_right2 f (fold_right2 f a0 l0 l'0) l l'.
Proof.
  induction l; destruct l'; inversion 1; cbn; eauto using f_equal.
Qed.

Lemma fold_left2_rev_right2 {A B B'}:
  forall (f: A -> B -> B' -> A) l l' a0,
    length l = length l' ->
    fold_left2 f l l' a0 =
    fold_right2 (fun b b' acc => f acc b b') a0 (rev l) (rev l').
Proof.
  induction l; destruct l'; inversion 1; cbn.
  - reflexivity.
  - rewrite fold_right2_app by (rewrite !rev_length; assumption).
    rewrite IHl; eauto.
Qed.

Section forall2.
   Context {A B: Type}.

   (* This doesn't generate good induction principles *)
   (* Inductive Forall2 (P : A -> B -> Prop) : list A -> list B -> Prop := *)
   (* | Forall_nil_l : forall lb, Forall2 P nil lb *)
   (* | Forall_nil_r : forall la, Forall2 P la nil *)
   (* | Forall_cons : forall a b la lb, P a b -> Forall2 P la lb -> Forall2 P (a :: la) (b :: lb). *)

   Definition forall2 (P: A -> B -> Prop) (lA: list A) (lB: list B) :=
     forall (n: nat) (a: A) (b: B),
       List.nth_error lA n = Some a ->
       List.nth_error lB n = Some b ->
       P a b.

   Lemma forall2_nil_l P :
     forall lb, forall2 P nil lb.
   Proof.
     unfold forall2; destruct n; cbn; inversion 1.
   Qed.

   Lemma forall2_nil_r P :
     forall la, forall2 P la nil.
   Proof.
     unfold forall2; destruct n; cbn; inversion 2.
   Qed.

   Lemma forall2_cons (P: A -> B -> Prop) :
     forall a b la lb,
       P a b ->
       forall2 P la lb ->
       forall2 P (a :: la) (b :: lb).
   Proof.
     unfold forall2; destruct n; cbn.
     - inversion 1; inversion 1; subst; eauto.
     - eauto.
   Qed.

   Lemma forall2_fold_left2' args:
     forall argSizes (P: _ -> _ -> Prop) Q,
       forall2 P args argSizes /\ Q ->
       fold_left2 (fun acc arg argSize => acc /\ P arg argSize) args argSizes Q.
   Proof.
     induction args; cbn; intros * (H & HP); destruct argSizes; try solve [intuition].
     eapply IHargs.
     repeat split; eauto.
     - intros n' **.
       apply (H (S n')); cbn; eauto.
     - apply (H 0); cbn; eauto.
   Qed.

   Lemma forall2_fold_left2 args:
     forall argSizes (P: _ -> _ -> Prop),
       forall2 P args argSizes ->
       fold_left2 (fun acc arg argSize => acc /\ P arg argSize) args argSizes True.
   Proof.
     eauto using forall2_fold_left2'.
   Qed.

   Lemma forall2_fold_right2' args:
     forall argSizes (P: _ -> _ -> Prop) Q,
       forall2 P args argSizes /\ Q ->
       fold_right2 (fun arg argSize acc => acc /\ P arg argSize) Q args argSizes.
   Proof.
     induction args; cbn; intros * (H & HP); destruct argSizes; try solve [intuition].
     split.
     - eapply IHargs; split; eauto.
       intros n' **; apply (H (S n')); cbn; eauto.
     - apply (H 0); cbn; eauto.
   Qed.

   Lemma forall2_fold_right2 args:
     forall argSizes (P: _ -> _ -> Prop),
       forall2 P args argSizes ->
       fold_right2 (fun arg argSize acc => acc /\ P arg argSize) True args argSizes.
   Proof.
     eauto using forall2_fold_right2'.
   Qed.

   Lemma fold_right2_forall2 (P: A -> B -> Prop):
     forall args argSizes Q,
       fold_right2 (fun arg argSize acc => acc /\ P arg argSize) Q args argSizes ->
       forall2 P args argSizes /\ Q.
   Proof.
     induction args; cbn; intros * H; destruct argSizes;
       try solve [intuition eauto using forall2_nil_l, forall2_nil_r].
     destruct H; destruct (IHargs argSizes Q ltac:(eassumption)).
     split; eauto using forall2_cons.
   Qed.
End forall2.
