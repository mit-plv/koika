Require Import SGA.Common SGA.Syntax SGA.Semantics SGA.TypedSyntax SGA.OneRuleAtATime.

Open Scope bool_scope.
Require Import Coq.Strings.String.
Open Scope string_scope.

Section Functions.
    Require Import List.
    Import ListNotations.

    Definition divide arg := match arg with
                             | [[a;b]] => [false;a]
                             | _ => []
                             end.
    Definition even arg := match arg with
                           | [[a;false]] => [true]
                           | [[a;true]] => [false]
                           | _ => []
                           end.

    Definition eq2 arg := match arg with
                           | [[a;b];[c;d]] =>
                             vbits [andb (Bool.eqb a c) (Bool.eqb b d)]
                           | _ => vtt
                           end.

    Definition odd arg := match arg with
                           | [[a;false]] => [false]
                           | [[a;true]] => [true]
                           | _ => []
                          end.
    Definition neg arg := match arg with
                           | [[false]] => vbits [true]
                           | [[true]] => vbits [false]
                           | _ => vtt
                          end.

    Definition threeNPlusOne arg := match arg with (* Fake implementation *)
                             | [[a;b]] => [b;false]
                             | _ => []
                             end.



End Functions.
(* Do not open List scope as we define a joli bind *)


Section Example1.
  Definition r := 0.
  Definition InitReg := putenv env_nil r (cons true (cons false nil)).
  Inductive Extfuns := Eq | Even | Odd | Divide | ThreeNPlusOne | Register  (idx: nat) | Neg | Fabst |Gabst |Streamabst.

  Scheme Equality for Extfuns.
  Definition SigmaEnv : Env Extfuns ExternalFunction := EqEnv Extfuns_eq_dec.

  Axiom magic : forall {A},A .
  Definition sigma : (SigmaEnv.(env_t)).
    refine (putenv _ Divide {| sig := {| argSizes := cons 2 nil;
                                         retType := 2 |};
                               impl := divide|}).
    refine (putenv _ ThreeNPlusOne {| sig := {| argSizes := cons 2 nil;
                                                retType := 2 |};
                                      impl := threeNPlusOne |}).
    refine (putenv _ Even {| sig := {| argSizes := cons 2 nil;
                                       retType := 1 |};
                             impl := even|}).
    refine (putenv _ Odd {| sig := {| argSizes := cons 2 nil;
                                      retType := 1 |};
                            impl := odd|}).

    exact env_nil.
    exact magic.
    exact magic.
    exact magic.
    exact magic.
  Defined.

  Delimit Scope sga_scope with sga.
  Notation "'Let' a '<-' b 'in' c" := (Bind a b c) (at level 99, c at level 98, only parsing) : sga_scope.
  Notation " a ';' b " :=  (Bind "nobodynamesavariablelikethat" a b) (at level 99): sga_scope. (* Hack *)
  Notation "reg '·' 'read_0'" := (Read P0 reg) (at level 99) :sga_scope.
  Notation "reg '·' 'read_1'" := (Read P1 reg) (at level 99) :sga_scope.
  Notation "reg '·' 'write_0(' value ')'" := (Write P0 reg value) (at level 99) :sga_scope.
  Notation "reg '·' 'write_1(' value ')'" := (Write P1 reg value) (at level 99) :sga_scope.
  Notation "f '[' arg ']'" := (Call f (cons arg nil)) (at level 99,arg at level 99) : sga_scope.
  Notation "f '<|' g" := (Try f%sga g g ) (at level 99, g at level 99, right associativity, only parsing).


  Definition divide_collatz :=
    (
      Let "v" <- r·read_0 in
        If (Even[Var"v"])
           (r·write_0(Divide[Var"v"]))
           Fail
    )%sga.

  Definition multiply_collatz :=
    (
      Let "v" <- r·read_1 in
        If (Odd[Var"v"])
           (r·write_1(Divide[Var"v"]))
           Fail
    )%sga.

  Definition collatz :=  divide_collatz <| multiply_collatz <| Done.
  Check collatz.

  Compute (interp_scheduler
           InitReg
           sigma
           nil
           collatz).

  Compute (interp_rule InitReg sigma env_nil nil nil divide_collatz).
  Compute (interp_rule InitReg sigma env_nil nil nil multiply_collatz).
End Example1.


Section Example2.
  Variable r0 r1: bool.
  Definition InitReg_abst := putenv env_nil r (cons r1 (cons r0 nil)).
  Variable divide_abst: list bits -> value.
  Variable threeNPlusOne_abst: list bits -> value.
  Variable even: list bits -> value.
    Variable odd: list bits -> value.
  Definition sigma_abst : (SigmaEnv.(env_t)).
    refine (putenv _ Divide {| sig := {| argSizes := cons 2 nil;
                                         retType := 2 |};
                               impl := divide_abst|}).
    refine (putenv _ ThreeNPlusOne {| sig := {| argSizes := cons 2 nil;
                                                retType := 2 |};
                                      impl := threeNPlusOne |}).
    refine (putenv _ Even {| sig := {| argSizes := cons 2 nil;
                                       retType := 1 |};
                             impl := even|}).
    refine (putenv _ Odd {| sig := {| argSizes := cons 2 nil;
                                      retType := 1 |};
                            impl := odd|}).

    exact env_nil.
    exact magic.
    exact magic.
    exact magic.
    exact magic.
  Defined.


  (* Redefine notations because they conflict with list and I do not know how to handle that properly without Custom_entries *)
  Delimit Scope sga_scope with sga.
  Notation "'Let' a '<-' b 'in' c" := (Bind a b c) (at level 99, c at level 98, only parsing) : sga_scope.
  Notation " a ';' b " :=  (Bind "nobodynamesavariablelikethat" a b) (at level 99): sga_scope. (* Hack *)
  Notation "reg '·' 'read_0'" := (Read P0 reg) (at level 99) :sga_scope.
  Notation "reg '·' 'read_1'" := (Read P1 reg) (at level 99) :sga_scope.
  Notation "reg '·' 'write_0(' value ')'" := (Write P0 reg value) (at level 99) :sga_scope.
  Notation "reg '·' 'write_1(' value ')'" := (Write P1 reg value) (at level 99) :sga_scope.
  Notation "f '[' arg ']'" := (Call f (cons arg nil)) (at level 99,arg at level 99) : sga_scope.
  Notation "f '<|' g" := (Try f%sga g g ) (at level 99, g at level 99, right associativity, only parsing).

  (* Test of notations: *)
  Check (Let "test" <- Skip in Skip)%sga.
  Check (Let "used" <- Fail in Var "used")%sga.
  Check ( Fail; Skip)%sga.
  Check (r·read_0)%sga.
  Check (r·write_0(Skip))%sga.
  Check (Let "used" <- r·read_0 in Var "used")%sga.
  Check (Even[Skip])%sga.
  Check (Skip <| Done).
  Check (Skip <| Fail <| Skip <| Done).
  Check ((r·read_0) <| Fail <| Skip <| r·write_0(Skip)<| Done).
  Check collatz.

  (* Manually we step through destructs to learn that those are the hypthesis that we need to reduce the computation *)
  Variable AEven : (forall r1 r0, { evenb & even ((r1 :: r0 :: nil) :: nil) = vbits (cons(evenb) nil)}) .

  Variable ADiv :  (forall r1 r0, { divide01 & divide_abst ((r1 :: r0 :: nil) :: nil)= vbits (cons (fst divide01) (cons (snd divide01) nil))}) .

  Variable AOdd : (forall dv1 dv0, { oddb & odd ((dv1 :: dv0 :: nil) :: nil) = vbits (cons(oddb) nil)}).
  (* Note that we do not need the relationship between Odd and Even at that level *)
  (* And nothing about Div *)

   Lemma caract_collatz : { t & (interp_scheduler
           InitReg_abst
           sigma_abst
           nil
           collatz) = t}.
     cbn.
     eexists.
     rewrite (projT2 (AEven r1 r0)).
     instantiate (1:=ltac:(destruct (projT1 (AEven r1 r0)))).
     (destruct (projT1 (AEven _ _))).
     cbn.
     rewrite (projT2 (ADiv _ _)).
     cbn.
     rewrite (projT2 (AOdd _ _)).
     cbn.
     instantiate (1:=ltac:(destruct (projT1 (AOdd (fst (projT1 (ADiv r1 r0))) (snd (projT1 (ADiv r1 r0))))))).
     destruct ( projT1 (AOdd (fst (projT1 (ADiv r1 r0))) (snd (projT1 (ADiv r1 r0))))).
     rewrite (projT2 (ADiv (fst (projT1 (ADiv r1 r0))) (snd (projT1 (ADiv r1 r0))))).
     cbn.
     reflexivity.
     cbn.
     reflexivity.
     rewrite (projT2 (AOdd _ _)).
     simpl.
     instantiate (1:=ltac:(destruct (projT1 (AOdd r1 r0)) )).
     destruct (projT1 (AOdd r1 r0)).
     cbn.
     rewrite (projT2(ADiv _ _)).
     simpl.
     reflexivity.
     simpl.
     reflexivity.
   Defined.
   Eval cbn in (projT1 caract_collatz).




   Compute (interp_rule InitReg sigma env_nil nil nil divide_collatz).
   Compute (interp_rule InitReg sigma env_nil nil nil multiply_collatz).
End Example2.



Section Example_Pipeline.
  Variable f_abst: list bits -> value.
  Variable g_abst: list bits -> value.
  Variable stream_abst: list bits -> value.
  Definition sigma2_abst : (SigmaEnv.(env_t)).
    refine (putenv _ Fabst {| sig := {| argSizes := cons 2 nil;
                                        retType := word 2 |};
                              impl := f_abst|}).
    refine (putenv _ Streamabst {| sig := {| argSizes := cons 2 nil;
                                             retType := word 2 |};
                                   impl := stream_abst |}).
    refine (putenv _ Neg {| sig := {| argSizes := cons 1 nil;
                                             retType := word 1 |};
                            impl := neg |}).
    refine (putenv _ Eq {| sig := {| argSizes := cons 2 (cons 2 nil);
                                             retType := word 1 |};
                                   impl := eq2 |}).

    refine (putenv _ Gabst {| sig := {| argSizes := cons 2 nil;
                                        retType := word 2 |};
                              impl := g_abst |}).

    exact env_nil.
    exact magic.
    exact magic.
    exact magic.
    exact magic.
    exact magic.
  Defined.


  (* Redefine notations because they conflict with list and I do not know how to handle that properly without Custom_entries *)
  Delimit Scope sga_scope with sga.
  Notation "'Let' a '<-' b 'in' c" := (Bind a b c) (at level 99, c at level 98) : sga_scope.
  Notation " a ';' b " :=  (Bind "nobodynamesavariablelikethat" a b) (at level 10, b at level 100): sga_scope. (* Hack *)
  Notation "reg '·' 'read_0'" := (Read P0 reg) (at level 10) :sga_scope.
  Notation "reg '·' 'read_1'" := (Read P1 reg) (at level 10) :sga_scope.
  Notation "reg '·' 'write_0(' value ')'" := (Write P0 reg value) (at level 10) :sga_scope.
  Notation "reg '·' 'write_1(' value ')'" := (Write P1 reg value) (at level 10) :sga_scope.
  Notation "f '[' arg ']'" := (Call f (cons arg nil)) (at level 99,arg at level 99) : sga_scope.
  Notation "f '[' arg1 ',' arg2 ']'" := (Call f (cons arg1 (cons arg2 nil))) (at level 99,arg1 at level 99, arg2 at level 99) : sga_scope.
  Notation "f '<|' g" := (Try f%sga g g ) (at level 99, g at level 99, right associativity, only parsing).

  (* Test of notations: *)
  Check (Let "test" <- Skip in Skip)%sga.
  Check (Let "used" <- Fail in Var "used" ; Skip)%sga.
  Check ( Fail; Skip)%sga.
  Check (r·read_0)%sga.
  Check (r·write_0(Skip))%sga.
  Check (Let "used" <- r·read_0 in Var "used")%sga.
  Check (Even[Skip])%sga.
  Check (Skip <| Done).
  Check (Skip <| Fail <| Skip <| Done).
  Check ((r·read_0) <| Fail <| Skip <| r·write_0(Skip)<| Done).
  Check collatz.
  (* Manually we step through destructs to learn that those are the hypthesis that we need to reduce the computation *)


  Definition outputReg := 2.
  Definition inputReg := 1.
  Definition invalid := 3.
  Definition correct:= 4.

  Definition  doF:=
    (Let "v" <- inputReg·read_0 in
     inputReg·write_0(Streamabst[Var"v"]);
     Let "invalid" <- invalid·read_1 in
     If (Var"invalid")
        (invalid·write_1(Const (cons false nil));
        r·write_0(Fabst[Var"v"]))
        Fail
    )%sga.

  Definition doG :=
    (
      Let "invalid" <- invalid·read_0 in
      If (Neg[Var"invalid"])
         (
           Let "data" <- r·read_0 in
           Let "v" <- outputReg·read_0 in
           (outputReg·write_0(Streamabst[Var"v"]));
           invalid·write_0(Const (cons true nil));
           If (Eq[Gabst[Var"data"],Gabst[Fabst[Var"v"]]])
              (Skip)
              (correct·write_0(Const (cons false nil)))
         )
         Fail
    )%sga.

  Definition Pipeline :=  doG <| doF <| Done.


  Variable r0 r1 d0 d1 inv : bool.
  Definition InitReg_1 := putenv (putenv (putenv (putenv (putenv env_nil correct (cons true nil)) invalid (cons inv nil)) inputReg (cons r1 (cons r0 nil))) outputReg (cons r1 (cons r0 nil))) r (cons d0 (cons d1 nil)).

  Variable AF :  (forall r1 r0, { v01 & f_abst ((r1 :: r0 :: nil) :: nil)= vbits (cons (fst v01) (cons (snd v01) nil))}) .

  Variable AG :  (forall r1 r0, { v01 & g_abst ((r1 :: r0 :: nil) :: nil)= vbits (cons (fst v01) (cons (snd v01) nil))}) .
  Variable AStream :  (forall r1 r0, { v01 & stream_abst ((r1 :: r0 :: nil) :: nil)= vbits (cons (fst v01) (cons (snd v01) nil))}) .

  
   Lemma caract_pipeline : {t & (interp_scheduler
           InitReg_1
           sigma2_abst
           nil
           Pipeline) = t}.
     cbn.
     eexists.
     instantiate (1:=ltac:(destruct inv)); destruct inv.
     cbn.
     rewrite (projT2 (AStream r1 r0)).
     cbn.
     rewrite (projT2 (AF _ _)).
     cbn.
     reflexivity.
     setoid_rewrite (projT2 (AStream r1 r0)).
     cbn.
     setoid_rewrite (projT2 (AG d0 d1)).
     cbn.
     rewrite (projT2 (AF r1 r0)).
     cbn.
     setoid_rewrite (projT2 (AG (fst (projT1 (AF r1 r0)))(snd (projT1 (AF r1 r0))))).
     cbn.
     instantiate (1:=ltac:( destruct (Bool.eqb (fst (projT1 (AG (fst (projT1 (AF r1 r0))) (snd (projT1 (AF r1 r0))))))
        (fst (projT1 (AG d0 d1))) &&
      Bool.eqb (snd (projT1 (AG (fst (projT1 (AF r1 r0))) (snd (projT1 (AF r1 r0))))))
      (snd (projT1 (AG d0 d1))))));     destruct (Bool.eqb (fst (projT1 (AG (fst (projT1 (AF r1 r0))) (snd (projT1 (AF r1 r0))))))
        (fst (projT1 (AG d0 d1))) &&
      Bool.eqb (snd (projT1 (AG (fst (projT1 (AF r1 r0))) (snd (projT1 (AF r1 r0))))))
      (snd (projT1 (AG d0 d1)))).
     -
     cbn.
     setoid_rewrite (projT2 (AStream r1 r0)).
     cbn.
     rewrite (projT2 (AF r1 r0)).
     cbn.
     reflexivity.
     -
       cbn.
       setoid_rewrite (projT2 (AStream r1 r0)).
       cbn.
       rewrite (projT2 (AF r1 r0)).
       cbn.
       reflexivity.
   Defined.
   Eval cbn in (projT1 caract_pipeline).

   Lemma caract_pipeline_update : {t & (interp_scheduler_trace_and_update
           InitReg_1
           sigma2_abst
           nil
           Pipeline) = t}.
     unfold interp_scheduler_trace_and_update.
     cbn.
     eexists.
     instantiate (1:=ltac:(destruct inv)); destruct inv.
     cbn.
     rewrite (projT2 (AStream r1 r0)).
     cbn.
     rewrite (projT2 (AF _ _)).
     cbn.
     reflexivity.
     setoid_rewrite (projT2 (AStream r1 r0)).
     cbn.
     setoid_rewrite (projT2 (AG d0 d1)).
     cbn.
     rewrite (projT2 (AF r1 r0)).
     cbn.
     setoid_rewrite (projT2 (AG (fst (projT1 (AF r1 r0)))(snd (projT1 (AF r1 r0))))).
     cbn.
     instantiate (1:=ltac:( destruct (Bool.eqb (fst (projT1 (AG (fst (projT1 (AF r1 r0))) (snd (projT1 (AF r1 r0))))))
        (fst (projT1 (AG d0 d1))) &&
      Bool.eqb (snd (projT1 (AG (fst (projT1 (AF r1 r0))) (snd (projT1 (AF r1 r0))))))
      (snd (projT1 (AG d0 d1))))));     destruct (Bool.eqb (fst (projT1 (AG (fst (projT1 (AF r1 r0))) (snd (projT1 (AF r1 r0))))))
        (fst (projT1 (AG d0 d1))) &&
      Bool.eqb (snd (projT1 (AG (fst (projT1 (AF r1 r0))) (snd (projT1 (AF r1 r0))))))
      (snd (projT1 (AG d0 d1)))).
     -
     cbn.
     setoid_rewrite (projT2 (AStream r1 r0)).
     cbn.
     rewrite (projT2 (AF r1 r0)).
     cbn.
     reflexivity.
     -
       cbn.
       setoid_rewrite (projT2 (AStream r1 r0)).
       cbn.
       rewrite (projT2 (AF r1 r0)).
       cbn.
       reflexivity.
   Defined.
   Eval cbn in  (projT1 caract_pipeline_update).
   (* So we need to prove that starting from $v$ = false, we will never reach a case where  *)
   (* From that we get that the condition for the two rules to fire simultaneously is $v$ *)
(*       We also get that the condition for the correctness is *)

(*        not v ->   Bool.eqb (fst (projT1 (AG (fst (projT1 (AF r1 r0))) (snd (projT1 (AF r1 r0)))))) *)
(*            (fst (projT1 (AG d0 d1))) && *)
(*          Bool.eqb (snd (projT1 (AG (fst (projT1 (AF r1 r0))) (snd (projT1 (AF r1 r0)))))) *)
(*            (snd (projT1 (AG d0 d1))). *)

   (* We end up having to prove that v is kept the rest of the time *)
   (* Indeed we end up with
         Bool.eqb (fst (projT1 (AG (fst (projT1 (AF r1 r0))) (snd (projT1 (AF r1 r0))))))
           (fst (projT1 (AG d0 d1))) &&
         Bool.eqb (snd (projT1 (AG (fst (projT1 (AF r1 r0))) (snd (projT1 (AF r1 r0))))))
           (snd (projT1 (AG d0 d1)))
 *)


   Compute (interp_rule InitReg sigma env_nil nil nil divide_collatz).
   Compute (interp_rule InitReg sigma env_nil nil nil multiply_collatz).
End Example2.



  Variable r0 r1 d0 d1 v c: bool.
  Definition InitReg_1 := putenv (putenv (putenv (putenv (putenv env_nil correct (cons c nil)) invalid (cons true nil)) inputReg (cons r1 (cons r0 nil))) outputReg (cons r1 (cons r0 nil))) r (cons d0 (cons d1 nil)).

  Variable AF :  (forall r1 r0, { v01 & f_abst ((r1 :: r0 :: nil) :: nil)= vbits (cons (fst v01) (cons (snd v01) nil))}) .

  Variable AG :  (forall r1 r0, { v01 & g_abst ((r1 :: r0 :: nil) :: nil)= vbits (cons (fst v01) (cons (snd v01) nil))}) .
  Variable AStream :  (forall r1 r0, { v01 & stream_abst ((r1 :: r0 :: nil) :: nil)= vbits (cons (fst v01) (cons (snd v01) nil))}) .
  (* Note that we do not need the relationship between Odd and Even at that level *)
  (* And nothing about Div *)

   Lemma caract_pipeline : {t & (interp_scheduler
           InitReg_1
           sigma2_abst
           nil
           Pipeline) = t}.
     cbn.
     eexists.
     instantiate (1:=ltac:(destruct v)); destruct v.
     cbn.
     rewrite (projT2 (AStream r1 r0)).
     cbn.
     rewrite (projT2 (AF _ _)).
     cbn.
     reflexivity.
     setoid_rewrite (projT2 (AStream r1 r0)).
     cbn.
     setoid_rewrite (projT2 (AG d0 d1)).
     cbn.
     rewrite (projT2 (AF r1 r0)).
     cbn.
     setoid_rewrite (projT2 (AG (fst (projT1 (AF r1 r0)))(snd (projT1 (AF r1 r0))))).
     cbn.
     instantiate (1:=ltac:( destruct (Bool.eqb (fst (projT1 (AG (fst (projT1 (AF r1 r0))) (snd (projT1 (AF r1 r0))))))
        (fst (projT1 (AG d0 d1))) &&
      Bool.eqb (snd (projT1 (AG (fst (projT1 (AF r1 r0))) (snd (projT1 (AF r1 r0))))))
      (snd (projT1 (AG d0 d1))))));     destruct (Bool.eqb (fst (projT1 (AG (fst (projT1 (AF r1 r0))) (snd (projT1 (AF r1 r0))))))
        (fst (projT1 (AG d0 d1))) &&
      Bool.eqb (snd (projT1 (AG (fst (projT1 (AF r1 r0))) (snd (projT1 (AF r1 r0))))))
      (snd (projT1 (AG d0 d1)))).
     -
     cbn.
     setoid_rewrite (projT2 (AStream r1 r0)).
     cbn.
     rewrite (projT2 (AF r1 r0)).
     cbn.
     reflexivity.
     -
       cbn.
       setoid_rewrite (projT2 (AStream r1 r0)).
       cbn.
       rewrite (projT2 (AF r1 r0)).
       cbn.
       reflexivity.
   Defined.
   Eval cbn in (projT1 caract_pipeline).

   Lemma caract_pipeline_update : {t & (interp_scheduler_trace_and_update
           InitReg_1
           sigma2_abst
           nil
           Pipeline) = t}.
     unfold interp_scheduler_trace_and_update.
     cbn.
     eexists.
     instantiate (1:=ltac:(destruct v)); destruct v.
     cbn.
     rewrite (projT2 (AStream r1 r0)).
     cbn.
     rewrite (projT2 (AF _ _)).
     cbn.
     reflexivity.
     setoid_rewrite (projT2 (AStream r1 r0)).
     cbn.
     setoid_rewrite (projT2 (AG d0 d1)).
     cbn.
     rewrite (projT2 (AF r1 r0)).
     cbn.
     setoid_rewrite (projT2 (AG (fst (projT1 (AF r1 r0)))(snd (projT1 (AF r1 r0))))).
     cbn.
     instantiate (1:=ltac:( destruct (Bool.eqb (fst (projT1 (AG (fst (projT1 (AF r1 r0))) (snd (projT1 (AF r1 r0))))))
        (fst (projT1 (AG d0 d1))) &&
      Bool.eqb (snd (projT1 (AG (fst (projT1 (AF r1 r0))) (snd (projT1 (AF r1 r0))))))
      (snd (projT1 (AG d0 d1))))));     destruct (Bool.eqb (fst (projT1 (AG (fst (projT1 (AF r1 r0))) (snd (projT1 (AF r1 r0))))))
        (fst (projT1 (AG d0 d1))) &&
      Bool.eqb (snd (projT1 (AG (fst (projT1 (AF r1 r0))) (snd (projT1 (AF r1 r0))))))
      (snd (projT1 (AG d0 d1)))).
     -
     cbn.
     setoid_rewrite (projT2 (AStream r1 r0)).
     cbn.
     rewrite (projT2 (AF r1 r0)).
     cbn.
     reflexivity.
     -
       cbn.
       setoid_rewrite (projT2 (AStream r1 r0)).
       cbn.
       rewrite (projT2 (AF r1 r0)).
       cbn.
       reflexivity.
   Defined.
   Eval cbn in  (projT1 caract_pipeline_update).
