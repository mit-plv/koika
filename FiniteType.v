Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Import ListNotations.

Class FiniteType {T} :=
  { finite_index: T -> nat;
    finite_elements: list T;
    finite_surjective: forall a: T, List.nth_error finite_elements (finite_index a) = Some a;
    finite_injective: NoDup (List.map finite_index finite_elements) }.
Arguments FiniteType: clear implicits.

Definition finite_index_injective {T: Type} {FT: FiniteType T}:
  forall t1 t2,
    finite_index t1 = finite_index t2 ->
    t1 = t2.
Proof.
  intros t1 t2 H.
  apply (f_equal (nth_error finite_elements)) in H.
  rewrite !finite_surjective in H.
  inversion H; auto.
Qed.

Definition finite_nodup {T} {FT: FiniteType T} :
  NoDup finite_elements.
Proof.
  eapply NoDup_map_inv.
  apply finite_injective.
Qed.

Fixpoint increasing' n (l: list nat) :=
  match l with
  | [] => true
  | n' :: l => andb (Nat.ltb n n') (increasing' n' l)
  end.

Definition increasing (l: list nat) :=
  match l with
  | [] => true
  | n :: l => increasing' n l
  end.

Lemma increasing'_not_In :
  forall l n, increasing' n l = true -> forall n', n' <= n -> ~ In n' l.
Proof.
  induction l; intros n H n' Hle Habs.
  - auto.
  - apply Bool.andb_true_iff in H; destruct H.
    destruct Habs; subst; apply PeanoNat.Nat.ltb_lt in H.
    + omega.
    + unfold not in IHl; eapply IHl;
        [ eassumption | .. | eassumption ]; omega.
Qed.

Lemma increasing'_NoDup :
  forall l n, increasing' n l = true -> NoDup l.
Proof.
  induction l; cbn; intros n H.
  - constructor.
  - apply Bool.andb_true_iff in H; destruct H.
    econstructor; eauto using increasing'_not_In.
Qed.

Lemma increasing_NoDup :
  forall l, increasing l = true -> NoDup l.
Proof.
  destruct l.
  - econstructor.
  - cbn; econstructor; eauto using increasing'_NoDup, increasing'_not_In.
Qed.

Lemma nth_error_app_l :
  forall {A} (l l' : list A) n x,
    nth_error l n = Some x ->
    nth_error (l ++ l') n = Some x.
Proof.
  induction l; destruct n; cbn;
    (solve [inversion 1] || eauto).
Qed.

Ltac list_length l :=
  lazymatch l with
  | _ :: ?tl => let len := list_length tl in constr:(S len)
  | _ => constr:(0)
  end.

Inductive FiniteType_norec (T: Type) :=
  | finite_type_norec : FiniteType_norec T.

Ltac FiniteType_t_compute_index :=
  vm_compute;
  lazymatch goal with
  | [  |- _ ?l ?idx = Some ?x ] =>
    let len := list_length l in
    match x with
    | ?f ?y =>
      let tx := type of x in
      let idx' := fresh "index" in
      evar (idx': nat); unify idx (len + idx'); subst idx';
      vm_compute; apply nth_error_app_l, map_nth_error;
      (* Must call typeclasses eauto manually, because plain typeclass resolution
         doesn't operate in the current context (and so FiniteType_norec isn't
         taken into account). *)
      pose proof (finite_type_norec tx);
      eapply (finite_surjective (FiniteType := ltac:(typeclasses eauto)))
    | ?x => instantiate (1 := len);
           instantiate (1 := _ :: _);
           vm_compute; reflexivity
    | _ => idtac
    end
  end.

(* This variant uses a counter shared between all goals to compute indices faster: *)
(* Fixpoint symmetric_plus (x y: nat) := *)
(*   match x with *)
(*   | O => y *)
(*   | S x => symmetric_plus x (S y) *)
(*   end. *)
(* Ltac finite_compute_index' counter := *)
(*   try (compute in counter; *)
(*        match (eval unfold counter in counter) with *)
(*        | symmetric_plus ?n ?cst => *)
(*          instantiate (1 := S _) in (Value of counter); *)
(*          lazymatch goal with *)
(*          | [  |- nth_error ?l ?idx = _ ] => *)
(*            unify idx cst; cbn; instantiate (1 := (_ :: _)); reflexivity *)
(*          end *)
(*        end). *)

Ltac FiniteType_t_nodup_increasing :=
  apply increasing_NoDup;
  vm_compute; reflexivity.

Ltac FiniteType_t_init :=
  unshelve econstructor;
    [ destruct 1; shelve | shelve | .. ].

Ltac FiniteType_t :=
  lazymatch goal with
  | [ H: FiniteType_norec ?T |- FiniteType ?T ] => fail "Type" T "is recursive"
  | [  |- FiniteType ?T ] =>
    let nm := fresh in
    FiniteType_t_init;
    [ intros nm; destruct nm; [> FiniteType_t_compute_index ..] |
      instantiate (1 := []); FiniteType_t_nodup_increasing ];
    fold (@nth_error nat)
  end.

Hint Extern 1 (FiniteType _) => FiniteType_t : typeclass_instances.

Module Examples.
  Inductive t' := A | B.
  Inductive t'' := A' | B' (x': t') | C'.

  Instance t'f : FiniteType t'.
  Proof. FiniteType_t. Defined.

  Instance t''f: FiniteType t''.
  Proof. FiniteType_t. Defined.
End Examples.
