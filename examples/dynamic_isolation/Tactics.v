Require Import Koika.Frontend.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
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

  Ltac destruct_pair :=
    match goal with
    | [ P : _ * _ |- _ ] =>
      let p1 := fresh P in
      let p2 := fresh P in
      destruct P as [p1 p2]
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

  Ltac simplify_all :=
    simpl in *; simplify_tuples; subst; auto.

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
End General.

Export General.

(*! List Helpers !*)
Module ListHelpers
.
  Lemma NoDup_map_inj:
    forall {A} {B} {C} (f: A -> B) (g: B -> C) (xs: list A),
    FinFun.Injective g ->
    NoDup (map f xs) ->
    NoDup (map (fun x => g (f x)) xs).
  Proof.
    intros. rewrite<-map_map.
    apply FinFun.Injective_map_NoDup; auto.
  Qed.

  Lemma NoDup_map_succ :
    forall {A} f (xs: list A),
    NoDup (map f xs) ->
    NoDup (map (fun x => S (f x)) xs).
  Proof.
    intros; apply NoDup_map_inj; auto.
    unfold FinFun.Injective; intros.
    lia.
  Qed.

  Lemma NoDup_map_plus:
    forall {A} f (xs: list A) n,
    NoDup (map f xs) ->
    NoDup (map (fun x => n + (f x)) xs).
  Proof.
    intros; apply NoDup_map_inj; auto.
    unfold FinFun.Injective; intros.
    lia.
  Qed.

  Lemma nth_error_app_map :
    forall {A} {B} (xs: list A) (ys: list B) f n z,
    nth_error ys n = Some z ->
    nth_error (map f xs ++ ys) (List.length xs + n) = Some z.
  Proof.
    intros. induction xs; auto.
  Qed.

  Lemma In_lt :
    forall {A} (xs: list A) v f,
    (forall x, v < f x) ->
    In v (map (fun x => f x) xs) -> False.
  Proof.
    induction xs; simpl in *; auto.
    intuition.
    - specialize H with (x := a); lia.
    - eapply IHxs; eauto.
  Qed.

  Lemma no_dup_increasing_app:
    forall xs ys ,
    (exists v, (forall x, (In x xs -> x < v)) /\
           (forall y, ((In y ys -> y >= v)))) ->
    NoDup xs ->
    NoDup ys ->
    NoDup (xs ++ ys).
  Proof.
    intros. induction xs.
    - simpl in *. auto.
    - simpl in *. apply NoDup_cons.
      + intuition.
        rewrite NoDup_cons_iff in *. propositional.
        apply in_app_or in H2. intuition.
        specialize H4 with (1 := or_introl eq_refl).
        specialize H5 with (1 := H). lia.
      + apply IHxs.
        * propositional. exists v; auto.
        * rewrite NoDup_cons_iff in H0; propositional; auto.
  Qed.
End ListHelpers.

Export ListHelpers.

Module FiniteTypeHelpers.

  Ltac list_length' l :=
    lazymatch l with
    | (map _ ?xs) ++ ?tl => let len := list_length' tl in constr:(List.length xs + len)
    | _ :: ?tl => let len := list_length' tl in constr:(1 + len)
    | _ => constr:(0)
    end.

  Ltac clean_up_zeroes :=
    match goal with
    | |- context[?x + 0] =>
      replace (x + 0) with x by auto
    end.

  Ltac FiniteType_t_compute_index' :=
    lazymatch goal with
    | [ |- _ ?l ?idx = Some ?x] =>
        let len := list_length' l in
        match x with
        | ?x ?y =>
           let tx := type of x in
           let idx' := fresh "index" in
           evar (idx': nat); unify idx (len + idx'); subst idx';
           pose proof (FiniteType.finite_type_norec tx);
           repeat clean_up_zeroes;
           simpl; repeat rewrite plus_assoc_reverse; repeat (apply nth_error_app_map; simpl);
           apply nth_error_app_l, map_nth_error;
           lazymatch goal with
           | [ |- _ = Some ?z ] =>
             let tx' := type of z in
             eapply (finite_surjective (T := tx') (*(FiniteType := ltac:(typeclasses eauto))*) )
           end
        | ?x => instantiate (1 := len);
               instantiate (1 := _ :: _);
               repeat (simpl; apply nth_error_app_map); reflexivity
        | _ => idtac
        end
    end.

  Definition finite_index_lt_length {T: Type} {FT: FiniteType T}:
    forall t1 ,
      finite_index t1 < List.length finite_elements.
  Proof.
    intros.
    destruct FT.
    unfold FiniteType.finite_index. unfold FiniteType.finite_elements.
    specialize finite_surjective with (a := t1).
    apply nth_error_Some.
    rewrite finite_surjective. option_simpl.
  Qed.

  Ltac NoDup_increasing :=
    apply increasing_NoDup; simpl; repeat rewrite andb_true_intro; auto;
    repeat split; auto; rewrite Nat.ltb_lt; omega.

  Ltac FiniteType_t' :=
    lazymatch goal with
    | [ H: FiniteType_norec ?T |- FiniteType ?T ] => fail "Type" T "is recursive"
    | [  |- FiniteType ?T ] =>
      let nm := fresh in
      FiniteType_t_init;
      [ intros nm; destruct nm; FiniteType_t_compute_index' |
        instantiate (1 := []);
        try rewrite List.app_nil_r;
        simpl;
        repeat match goal with
        | [ |- NoDup [] ] =>
            constructor
        | [ |- NoDup (_ :: _) ] =>
            apply NoDup_cons
        | [ |- not _ ] =>
            unfold not; intros
        | [ H: In ?V (map _ ?elems) |- _ ] =>
          eapply In_lt with (v := V); [ | eapply H];
          intros; omega
        | [ |- context[_ + 0] ] =>
          repeat rewrite Nat.add_0_r
        | [ |- exists _, _ ] =>
          eexists; try split_cases; intros
        | [ H: In ?x (map _ _) |- _ ] =>
          eapply in_map_iff in H; propositional; subst
        | [ H: In ?x0 (@finite_elements _ _) |- _ ] =>
          pose proof (finite_index_lt_length x0);
          repeat eapply lt_n_S; solve[eauto; lia]
        | [ H: In ?x0 (@finite_elements _ _) |- _ ] =>
          pose proof (finite_index_lt_length x0);
          repeat eapply lt_n_S;
          match goal with
          | H: @finite_index ?t1 ?t2 ?x0 < ?v |- ?a + (@finite_index ?t1 ?t2 ?x0) < _ =>
              instantiate (1 := a + v); omega
          end
        | [ H: In _ _ |- _] =>
            progress (repeat rewrite map_app in H;
                      repeat apply in_app_or in H;
                      repeat rewrite map_map in H;
                      simpl in *;
                      split_cases)
        | [ |- _ ] =>
          try lia;
          progress (repeat (try rewrite map_app; try rewrite map_map; simpl);
                    repeat (apply no_dup_increasing_app; simpl; try NoDup_increasing);
                    repeat (apply NoDup_map_plus  ||  apply NoDup_map_succ); try apply finite_injective)
        end]
     end; try lia.

  Hint Extern 5 (FiniteType _) => FiniteType_t' : typeclass_instances.

End FiniteTypeHelpers.


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
