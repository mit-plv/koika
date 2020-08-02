Require Import Koika.Frontend.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Program.Equality.
Require Import EquivDec.

Module General.
  Ltac simpl_match :=
    let repl_match_goal d d' :=
        replace d with d';
        lazymatch goal with
        | [ |- context[match d' with _ => _ end] ] => fail
        | _ => idtac
        end in
    let repl_match_hyp H d d' :=
        replace d with d' in H;
        lazymatch type of H with
        | context[match d' with _ => _ end] => fail
        | _ => idtac
        end in
    match goal with
    | [ Heq: ?d = ?d' |- context[match ?d with _ => _ end] ] =>
        repl_match_goal d d'
    | [ Heq: ?d' = ?d |- context[match ?d with _ => _ end] ] =>
        repl_match_goal d d'
    | [ Heq: ?d = ?d', H: context[match ?d with _ => _ end] |- _ ] =>
        repl_match_hyp H d d'
    | [ Heq: ?d' = ?d, H: context[match ?d with _ => _ end] |- _ ] =>
        repl_match_hyp H d d'
    end.

  Ltac destruct_matches_in e :=
    lazymatch e with
    | context[match ?d with | _ => _ end] =>
        destruct_matches_in d
    | _ =>
        destruct e eqn:?; intros
    end.

  Ltac destruct_matches_in_hyp H :=
    lazymatch type of H with
    | context[match ?d with | _ => _ end] =>
        destruct_matches_in d
    | ?v =>
        let H1 := fresh H in
        destruct v eqn:H1; intros
    end.


  Ltac destruct_all_matches :=
    repeat (try simpl_match;
            try match goal with
                | [ |- context[match ?d with | _ => _ end] ] =>
                    destruct_matches_in d
                | [ H: context[match ?d with | _ => _ end] |- _ ] =>
                    destruct_matches_in d
                end);
    subst;
    try congruence;
    auto.

  Ltac destruct_nongoal_matches :=
    repeat (try simpl_match;
            try match goal with
            | [ H: context[match ?d with | _ => _ end] |- _ ] =>
                destruct_matches_in d
                end);
    subst;
    try congruence;
    auto.

  Ltac fast_destruct_goal_matches :=
    repeat (match goal with
            | [ |- context[match ?d with | _ => _ end] ] =>
                destruct_matches_in d
            end)
    .

  Ltac fast_destruct_nongoal_matches :=
    repeat (match goal with
            | [ H: context[match ?d with | _ => _ end] |- _ ] =>
                destruct_matches_in d
                end).


  Ltac destruct_goal_matches :=
    repeat (try simpl_match;
            match goal with
            | [ |- context[match ?d with | _ => _ end] ] =>
                destruct_matches_in d
            end);
    try congruence;
    auto.

  Tactic Notation "destruct" "matches" "in" "*" := destruct_all_matches.
  Tactic Notation "destruct" "matches" "in" "*|-" := destruct_nongoal_matches.
  Tactic Notation "destruct" "matches" := destruct_goal_matches.

  Ltac match_innermost_in H :=
    match type of H with
    | context[match ?E with _ => _ end] =>
      match E with
      | context[match _ with _ => _ end] => fail 1
      | _ => destruct E eqn:?; simpl in *
      end
    end; subst; try congruence; eauto.

  Ltac match_innermost_in_goal :=
    match goal with
    | [ |- context[match ?E with _ => _ end] ]=>
      match E with
      | context[match _ with _ => _ end] => fail 1
      | _ => destruct E eqn:?; simpl in *
      end
    end; subst; try congruence; eauto.

  Ltac fast_match_innermost_in_goal :=
      match goal with
      | [ |- context[match ?E with _ => _ end] ]=>
        match E with
        | context[match _ with _ => _ end] => fail 1
        | _ => destruct E eqn:?
        end
      end.

  Ltac destruct_one_match_in H :=
    lazymatch type of H with
    | context[match ?d with | _ => _ end] =>
        let H1 := fresh H in
        destruct d eqn:H1
    end.

  Ltac destruct_pair :=
    match goal with
    | [ P : _ * _ |- _ ] =>
      let p1 := fresh P in
      let p2 := fresh P in
      destruct P as [p1 p2]
  end.

  Ltac destruct_pairs := repeat destruct_pair.

  Ltac destruct_one_ind :=
    match goal with
    | [ H: ?T |- _ ] => is_ind T; destruct H
    end.

  Ltac destruct_inds := repeat destruct_one_ind.

  Ltac destruct_rightmost_var term :=
    lazymatch term with
    | ?f ?x =>
        destruct_rightmost_var x
    | ?x => is_var x; destruct x
    end.

  Ltac destruct_one_var_with t :=
    match goal with
    | [ H: ?T |- _ ] => is_var H; destruct H; try t
    end.

  Ltac destruct_vars_with t :=
    repeat (destruct_one_var_with t).

  Tactic Notation "destruct_one_var" := destruct_one_var_with auto.
  Tactic Notation "destruct_vars_with" tactic(t) := repeat (destruct_one_var_with t).
  Tactic Notation "destruct_vars" := destruct_vars_with auto.

  Ltac solve' :=
    match goal with
    | |- ?x = (fst ?x, snd ?x) =>
      destruct x; reflexivity
    | [ H: False |- _ ] => solve [ destruct H ]
    | [ H: ?P |- ?P ] => exact H
    end.





  Ltac propositional_with t :=
    repeat match goal with
    | [ H : _ /\ _  |- _ ] =>
        let H1 := fresh H in
        let H2 := fresh H in
        destruct H as [H1 H2]
    | [ H : _ <-> _  |- _ ] =>
        let H1 := fresh H in
        let H2 := fresh H in
        destruct H as [H1 H2]
    | |- forall _, _ => intros
    | [ H: False |- _ ] => solve [ destruct H ]
    | [ |- True ] => exact I
    | [ H : exists (varname: _ ), _ |- _ ] =>
        let newvar := fresh varname in
        let Hpref  := fresh H in
        destruct H as [newvar Hpref]
    | [ H: ?P -> _ |- _ ] =>
      lazymatch type of P with
      | Prop => match goal with
            | [ H': P |- _ ] => specialize (H H')
            | _ => specialize (H ltac:(try t))
            end
      end
    | [ H: forall x, x = _ -> _ |- _ ] =>
      specialize (H _ eq_refl)
    | [ H: forall x, _ = x -> _ |- _ ] =>
      specialize (H _ eq_refl)
    | [ H: exists (varname : _), _ |- _ ] =>
      let newvar := fresh varname in
      destruct H as [newvar ?]
    | [ H: ?P |- ?P ] => exact H
    | _ => progress subst
    | _ => solve [ t ]
    end.

  Tactic Notation "propositional" := propositional_with auto.
  Tactic Notation "propositional" tactic(t) := propositional_with t.

  Ltac split_cases :=
    repeat match goal with
    | |- _ /\ _ => split
    | [ H: _ \/ _ |- _ ] => destruct H
    | _ => progress propositional
    | _ => solve [ eauto ]
    end; try discriminate.

  Ltac consider f := unfold f in *.

  Lemma simple_tuple_inversion:
    forall {A} {B} (a: A) (b: B) x y,
    (a,b) = (x,y) ->
    a = x /\ b = y.
  Proof.
    intros. inversion H. auto.
  Qed.

  Ltac simplify_tuples :=
    repeat match goal with
    | [ H: (_,_) = (_,_) |- _ ] =>
      apply simple_tuple_inversion in H; destruct H
    end.

  Ltac simplify_tupless := simplify_tuples; subst.

  Ltac simplify_all :=
    simpl in *; simplify_tuples; subst; auto.

  Ltac subst_tuple_for t :=
    match goal with
    | H: _ = (t,?b) |- _ =>
      replace t with (fst (t,b)) by auto; rewrite<-H
    | H: _ = (?a,t) |- _ =>
      replace t with (snd (a,t)) by auto; rewrite<-H
    | H: _ = (?a,t,?c) |- _ =>
      replace t with (snd (fst(a,t,c))) by auto; rewrite<-H
    | H: _ = (t,?b,?c) |- _ =>
      replace t with (fst(fst(t,b,c))) by auto; rewrite<-H
    end.

  Definition is_some : forall {A}, option A -> Prop :=
    fun _ opt => exists v, opt = Some v.

  Definition is_none : forall {A}, option A -> Prop :=
    fun _ opt => opt = None.

  Lemma some_not_none : forall {A: Type} {a: A} {opt},
     opt = Some a -> opt <> None.
  Proof.
    cbv. intros; subst. inversion H0.
  Qed.

  Lemma not_none_is_some: forall {A : Type} {opt: option A},
    opt <> (@None A) -> exists a, opt = Some a.
  Proof.
    intros. destruct opt; eauto. destruct H; eauto.
  Qed.

  Lemma some_inj :
    forall A (x: A) (y: A),
    Some x = Some y ->
    x = y.
  Proof.
    intros. inversion H. auto.
  Qed.

  Ltac option_simpl :=
    unfold is_some in *; unfold is_none in *;
    repeat match goal with
    | [ H : Some _ = Some _  |- _ ] =>
      apply some_inj in H
    | [ H : Some _ = None |- _ ] =>
      inversion H
    | [ H : None = Some _ |- _ ] =>
      inversion H
    | [ H : None <> None |- _ ] =>
      destruct H
    | [ H : is_none _ |- _ ] =>
        unfold is_none in H
    | [ |- Some _ <> None ] =>
        let H := fresh in
        hnf; intro H; inversion H
    | [ |- Some _ = Some _] =>
        f_equal
    | [ H1: ?x = Some _,
        H2: ?x = Some _ |- _ ] =>
      rewrite H1 in H2; clear H1
    end.

  Ltac rewrite_term_from_tuple term :=
    match goal with
    | [H: _ = (term, ?y) |- _ ] =>
      replace term with (fst (term, y)) by auto;
      rewrite<-H
    | [H: _ = (?x, term) |- _ ] =>
      replace term with (snd (x, term)) by auto;
      rewrite<-H
    end.

  Ltac rewrite_in_goal :=
    repeat lazymatch goal with
    | H: ?x = ?x |- _ =>  fail 1
    | H: ?x = _ |- context[?x] =>
        rewrite H
    end.


  Ltac rewrite_solve :=
    match goal with
    | [ H: _ |- _ ] => solve[rewrite H; try congruence; auto]
    end.

  Ltac destruct_tuple :=
    match goal with
    | [ H: context[let '(a, b) := ?p in _] |- _ ] =>
      let a := fresh a in
      let b := fresh b in
      destruct p as [a b]
    | [ |- context[let '(a, b) := ?p in _] ] =>
      let a := fresh a in
      let b := fresh b in
      destruct p as [a b]
    end.

  Ltac safe_intuition_then t :=
    repeat match goal with
           | [ H: _ /\ _ |- _ ] =>
             destruct H
           | [ H: ?P -> _ |- _ ] =>
             lazymatch type of P with
             | Prop => specialize (H ltac:(t))
             | _ => fail
             end
           | [ |- not _ ] =>
             unfold not; intros
           | _ => progress t
           end.

  Tactic Notation "safe_intuition" := safe_intuition_then ltac:(auto).
  Tactic Notation "safe_intuition" tactic(t) := safe_intuition_then t.

  Ltac destruct_ands :=
    repeat match goal with
           | [ H: _ /\ _ |- _ ] =>
             destruct H
           end.

  Ltac deex :=
    match goal with
    | [ H : exists (varname : _), _ |- _ ] =>
      let newvar := fresh varname in
      destruct H as [newvar ?]; destruct_ands; subst
    end.

  Ltac split_or :=
    repeat match goal with
           | [ H: _ \/ _ |- _ ] => destruct H
           end.

  Ltac intuition_with t :=
    repeat match goal with
           | [ H: _ \/ _ |- _ ] => destruct H
           | [ |- not _ ] =>
             unfold not; intros
           | _ => progress propositional_with t
           | |- _ /\ _ => split
           | |- _ <-> _ => split
           | _ => t
           end.

  Tactic Notation "intuition" := intuition_with auto.
  Tactic Notation "intuition" tactic(t) := intuition_with t.

  Tactic Notation "assert_false" :=
    elimtype False.

  Ltac solve_false :=
    solve [ exfalso; eauto with false ].


  Hint Extern 10 => Equality.is_ground_goal; progress exfalso : core.

  Ltac especialize H :=
    match type of H with
    | forall (x:?T), _ =>
      let x := fresh x in
      evar (x:T);
      specialize (H x);
      subst x
    end.

  Ltac rename_by_type type name :=
    match goal with | x : type |- _ => rename x into name end.

  Ltac lia :=
  repeat match goal with
         | [ H: ?a <> ?a |- _ ] =>
           exfalso; apply (H eq_refl)
         | |- _ <> _ => let H := fresh in
                     intro H;
                     try rewrite H in *
         | [ n: ?t |- _ ] => progress change t with nat
         | [ H: @eq ?t _ _ |- _ ] =>
           progress change t with nat in H
         | [ H: ~ (@eq ?t _ _) |- _ ] =>
           progress change t with nat in H
         | [ |- @eq ?t _ _ ] =>
           progress change t with nat
         | [ |- ~ (@eq ?t _ _) ] =>
           progress change t with nat
         end; Lia.lia.

  Ltac dep_destruct E := let x := fresh "x" in
      remember E as x; simpl in x; dependent destruction x;
        try match goal with
              | [ H : _ = E |- _ ] => rewrite <- H in *; clear H
            end.

  Ltac auto_dep_destruct :=
    match goal with
    | H: context[match ?x as _ return _ with _ => _ end] |- _ =>
        dep_destruct x
    | |- context[match ?x as _ return _ with _ => _ end] =>
        dep_destruct x
    end.

End General.

Export General.

Module SimplMatchTests.

  (** test simpl_match failure when match does not go away *)
  Lemma fails_if_match_not_removed :
    forall (vd m: nat -> option nat) a,
      vd a = m a ->
      vd a = match (m a) with
             | Some v => Some v
             | None => None
             end.
  Proof.
    intros.
    (simpl_match; fail "should not work here")
    || idtac.
    rewrite H.
    destruct (m a); auto.
  Qed.

  Lemma removes_match :
    forall (vd m: nat -> option nat) a v v',
      vd a = Some v ->
      m a = Some v' ->
      vd a = match (m a) with
             | Some _ => Some v
             | None => None
             end.
  Proof.
    intros.
    simpl_match; now auto.
  Qed.

  (** hypothesis replacement should remove the match or fail *)
  Lemma fails_on_hyp_if_match_not_removed :
    forall (vd m: nat -> option nat) a,
      vd a = m a ->
      m a = match (m a) with
            | Some v => Some v
            | None => None
            end ->
      True.
  Proof.
    intros.
    (simpl_match; fail "should not work here")
    || idtac.
    trivial.
  Qed.

End SimplMatchTests.

Module DestructMatchesTests.

  Lemma removes_absurdities :
    forall b1 b2,
      b1 = b2 ->
      match b1 with
      | true => match b2 with
               | true => True
               | false => False
               end
      | false => match b2 with
                | true => False
                | false => True
                end
      end.
  Proof.
    intros.
    destruct_all_matches.
  Qed.

  Lemma destructs_innermost_match :
    forall b1 b2,
      match (match b2 with
             | true => b1
             | false => false
             end) with
      | true => b1 = true
      | false => b1 = false \/ b2 = false
      end.
  Proof.
    intros.
    destruct_goal_matches.
  Qed.

End DestructMatchesTests.


Module DeexTests.

  Lemma chooses_name :
    (exists (foo:unit), foo=foo) ->
    True.
  Proof.
    intros.
    deex.
    destruct foo.
    trivial.
  Qed.

  Lemma chooses_fresh_name :
    forall (foo:bool),
      (exists (foo:unit), foo=foo) -> True.
  Proof.
    intros.
    deex.
    (* fresh name for exists witness *)
    destruct foo0.
    trivial.
  Qed.

End DeexTests.
