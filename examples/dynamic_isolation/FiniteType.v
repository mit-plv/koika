Require Import Koika.Frontend.
Require Import Coq.Program.Wf.
Require Import dynamic_isolation.Tactics.
Require Import dynamic_isolation.Util.

Module FiniteTypeHelpers.

  Hint Rewrite map_map : FT_helpers.
  Hint Rewrite map_app : FT_helpers.
  Hint Rewrite map_cons : FT_helpers.
  Hint Rewrite Nat.add_0_r : FT_helpers.
  Hint Rewrite Nat.add_0_l : FT_helpers.
  Hint Rewrite @map_nil : FT_helpers.
  Hint Constructors NoDup : FT_helpers.
  Hint Rewrite app_nil_r : FT_helpers.

  Program Fixpoint increasing_lists (l: list (list nat)) {measure (length l)} : Prop :=
    match l with
    | [] => True
    | l1 :: [] => True
    | l1 :: ([] :: l3) =>
      increasing_lists (l1 :: l3)
    | l1 :: ((x :: xs) as l2 :: l3) =>
        Forall (fun n => Forall (lt n) l2) l1 /\
        increasing_lists (l2 :: l3)
    end.

  Ltac reduce_program_fixpoint t :=
    intros; unfold t; rewrite fix_sub_eq; simpl; fold t; auto;
    intros; repeat auto_dep_destruct; auto; apply f_equal; auto.

  Ltac reduce_program_fixpoint_in_hyp t H:=
    intros; unfold t in H; rewrite fix_sub_eq in H; simpl in H; fold t in H; auto;
    intros; repeat auto_dep_destruct; auto; apply f_equal; auto.

  Lemma increasing_lists_red0 :
    increasing_lists [].
  Proof.
    reduce_program_fixpoint increasing_lists.
  Qed.


  Lemma increasing_lists_red1 :
    forall l1, increasing_lists (l1 :: []).
  Proof.
    reduce_program_fixpoint increasing_lists.
  Qed.


  Lemma increasing_lists_red2 :
    forall l1 l3,
      increasing_lists (l1 :: l3) <->
      increasing_lists (l1 :: [] :: l3).
  Proof.
    split.
    - reduce_program_fixpoint increasing_lists.
    - intros. reduce_program_fixpoint_in_hyp increasing_lists H.
  Qed.

  Lemma increasing_lists_red3 :
    forall l1 l2 l3,
      l2 <> [] ->
      (Forall (fun n => Forall (lt n) l2) l1 /\
       increasing_lists (l2 :: l3) <->
       increasing_lists (l1 :: l2 :: l3)).
  Proof.
    split.
    - reduce_program_fixpoint increasing_lists.
    - intros. reduce_program_fixpoint_in_hyp increasing_lists H0.
  Qed.

  Hint Resolve increasing_lists_red0 : FT_helpers.
  Hint Resolve increasing_lists_red1 : FT_helpers.
  Hint Resolve increasing_lists_red2 : FT_helpers.
  Hint Resolve increasing_lists_red3 : FT_helpers.

  Ltac ftauto := auto with FT_helpers.

  Lemma increasing_lists_cons_nil :
    forall xss,
    increasing_lists xss <->
    increasing_lists ([] :: xss).
  Proof.
    split; intros.
    - destruct xss; auto.
      destruct l.
      + rewrite<-increasing_lists_red2; auto.
      + rewrite<-increasing_lists_red3; auto.
        congruence.
    - destruct xss; auto.
      destruct l; auto.
      + rewrite<-increasing_lists_red2 in H. auto.
      + rewrite<-increasing_lists_red3 in H; propositional; congruence.
  Qed.

  Lemma increasing_lists_cons :
    forall xss xs,
    increasing_lists (xs :: xss) ->
    increasing_lists xss.
  Proof.
    induction xss; simpl; intros; auto.
    destruct a.
    - rewrite<-increasing_lists_cons_nil.
      rewrite<-increasing_lists_red2 in H.
      eapply IHxss; eauto.
    - rewrite<-increasing_lists_red3 in H; propositional; congruence.
  Qed.

  Lemma increasing_lists_cons2 :
    forall xss x xs ,
    increasing_lists ((x::xs) :: xss) ->
    increasing_lists (xs::xss).
  Proof.
    induction xss.
    - auto.
    - simpl; intros; auto.
      destruct a.
      + rewrite<-increasing_lists_red2 in *.
        eapply IHxss; eauto.
      + rewrite<-increasing_lists_red3 in *; intuition; try congruence.
        inversion H0; auto.
  Qed.

  (* TODO: ugly proof *)
  Lemma increasing_lists_cons3 :
    forall xss xs2 xs1 ,
    increasing_lists (xs1 :: xs2 :: xss) ->
    increasing_lists (xs1 :: xss).
  Proof.
    induction xss.
    - intros; apply increasing_lists_red1.
    - intros.
      generalize dependent xs1.
      generalize dependent xs2.
      destruct a.
      + intros. rewrite<-increasing_lists_red2.
        eapply IHxss with (xs2 := xs2).
        destruct xs2.
        { rewrite<-increasing_lists_red2 in H. auto. }
        { rewrite<-increasing_lists_red3 in H; propositional; try congruence.
          rewrite<-increasing_lists_red2 in H1.
          rewrite<-increasing_lists_red3; propositional; try congruence.
        }
      + destruct xs2.
        { intros. rewrite<-increasing_lists_red2 in H. auto. }
        { intros. rewrite<-increasing_lists_red3 in H; propositional; try congruence.
          rewrite<-increasing_lists_red3; intuition; try congruence.
          { rewrite<-increasing_lists_red3 in H1; intuition; try congruence.
            rewrite Forall_forall in *.
            intros. rewrite Forall_forall; intros.
            specialize H0 with (1 := H). rewrite Forall_forall in *.
            specialize H0 with (x0 := n0); simpl in H0; intuition.
            specialize H2 with (x := n0); simpl in H2; intuition.
            rewrite Forall_forall in *.
            specialize H2 with (1 := H1).
            lia.
          }
          { eapply increasing_lists_cons; eauto. }
        }
  Qed.

  Lemma increasing_lists_impl_lt_concat :
    forall xs xss,
    increasing_lists (xs :: xss) ->
    Forall (fun n => Forall (lt n) (concat xss)) xs.
  Proof.
    induction xs.
    - simpl; auto.
    - induction xss; intros; auto.
      + simpl; constructor; auto.
        clear; induction xs; auto.
      + rewrite Forall_forall in *; intros.
        simpl.
        apply Forall_app.
        { destruct a0; auto.
          rewrite<-increasing_lists_red3 in H; propositional; try congruence.
          rewrite Forall_forall in H1. auto.
        }
        { apply IHxss; auto.
          eapply increasing_lists_cons3 in H; eauto.
        }
  Qed.

  Definition NoDup_increasing_lists :
    forall l,
      Forall (@NoDup nat) l ->
      increasing_lists l ->
      NoDup (concat l).
  Proof.
    induction l.
    - intros; simpl; auto with FT_helpers.
    - intros; simpl; auto with FT_helpers.
      generalize dependent l.
      induction a.
      + intros; simpl.
        apply IHl; auto.
        inversion H; auto.
        apply increasing_lists_cons with (xs := []); auto.
      + intros.
        inversion H; subst.
        rewrite<-app_comm_cons.
        constructor.
        { rewrite NoDup_cons_iff in *; propositional.
          unfold not in *; intuition.
          rewrite in_app_iff in *.
          intuition.
          apply increasing_lists_impl_lt_concat in H0.
          inversion H0; subst.
          rewrite Forall_forall in H7.
          specialize H7 with (1 := H3).
          lia.
        }
        { apply IHa; auto.
          { constructor; auto.
            inversion H3; auto.
          }
          { eapply increasing_lists_cons2; eauto. }
        }
  Qed.

  Ltac replace_cons_with_app :=
      repeat match goal with
      | |- context[?x :: ?xs] =>
          match xs with
          | [] => fail 1
          | _ => rewrite (@cons_app nat x xs)
          end
      end.

  (* x1 ++ x2 ++ x3 ===> concat [x1;x2;x3] *)
  Ltac replace_app_with_concat_list t :=
    lazymatch t with
    | app ?x1 ?x2 =>
        let tmp := ltac:(replace_app_with_concat_list x2) in
        constr:(cons x1 tmp)
    | ?x => constr:([x])
    end.


  Lemma Forall_lt_map :
    forall {A} xs v (f: A -> nat),
    (forall a, lt v (f a)) ->
    Forall (lt v) (map f xs).
  Proof.
    induction xs.
    - simpl; auto.
    - simpl; intros.
      constructor; auto.
  Qed.

  Lemma Forall_lt_map_forall :
    forall {A} {B} xs ys (f: A -> nat) (g: B -> nat),
    (forall a b, lt (f a) (g b)) ->
    Forall (fun n => Forall (lt n) (map g ys)) (map f xs).
  Proof.
    intros; rewrite Forall_forall.
    intros.
    apply Forall_lt_map.
    rewrite in_map_iff in H0; propositional.
  Qed.

  Lemma Forall_lt_forall :
    forall {A} xs ys (f: A -> nat),
    (forall a, Forall (lt (f a)) ys) ->
    Forall (fun n => Forall (lt n) ys) (map f xs).
  Proof.
    intros; rewrite Forall_forall.
    intros.
    rewrite in_map_iff in H0; propositional.
  Qed.
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

  Ltac reduce_increasing_lists :=
      match goal with
      | |- increasing_lists [] => solve[apply increasing_lists_red0]
      | |- increasing_lists [_] => solve[apply increasing_lists_red1]
      | |- increasing_lists (?l1 :: ?l2 :: ?l3) => rewrite<-increasing_lists_red3; [ split | discriminate]
      | |- increasing_lists (?l1 :: ?l2 :: ?l3) =>
          let Heq := fresh in
          destruct l2 eqn:Heq; [ rewrite<-increasing_lists_red2
                               | rewrite<-increasing_lists_red3; [ split | discriminate ]; rewrite<-Heq]
      end.

  Ltac FT_NoDup_solve :=
    replace_cons_with_app;
    match goal with
    | |- NoDup ?xs =>
        let y := replace_app_with_concat_list xs in
        let z := constr:(concat y) in
        replace xs with z by (unfold concat; autorewrite with FT_helpers; auto)
    end;
    apply NoDup_increasing_lists;
    [ repeat apply Forall_cons;
      repeat match goal with
         | |- NoDup (map (fun _ => _ + _) ?x) =>
           apply NoDup_map_plus
         | |- NoDup (map (@finite_index ?T ?FT) _) =>
           apply (@finite_injective T FT)
         | |- NoDup [?x]  =>
           apply NoDup_single_elem
         | _ => auto with FT_helpers
         end
    | repeat reduce_increasing_lists;
      repeat match goal with
      | |- Forall (lt _) (map _ _ ) =>
          apply Forall_lt_map
      | |- Forall (fun _ => Forall (lt _) (map _ _)) (map _ _ ) =>
          apply Forall_lt_map_forall
      | |- Forall (fun _ => Forall (lt _) _) (map _ _ ) =>
          apply Forall_lt_forall
      | |- forall _, _ => intros
      | |- context[@finite_index ?T ?FT ?v]  =>
        pose proof (@FiniteTypeHelpers.finite_index_lt_length T FT v); lia
      | |- Forall _ (_ :: _) => constructor
      | |- Forall _ [] => constructor
      end; try lia; discriminate
    ].

  Ltac FiniteType_t'' :=
      lazymatch goal with
      | [ H: FiniteType_norec ?T |- FiniteType ?T ] => fail "Type" T "is recursive"
      | [ |- FiniteType ?T ] =>
        let nm := fresh in
        FiniteType_t_init;
          [ intros nm; destruct nm; FiniteType_t_compute_index' |
            instantiate (1 := []);
            try rewrite List.app_nil_r;
            autorewrite with FT_helpers;
            FT_NoDup_solve
          ]
     end.
  Hint Extern 1 (FiniteType _) => FiniteType_t'' : typeclass_instances.




  (*
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
     *)
  (* Hint Extern 5 (FiniteType _) => FiniteType_t' : typeclass_instances. *)

End FiniteTypeHelpers.
