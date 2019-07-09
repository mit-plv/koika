Require Import SGA.Common SGA.Environments SGA.Syntax SGA.Semantics SGA.Types.

Open Scope bool_scope.
Require Import Coq.Strings.String.
Open Scope string_scope.

Section Functions.
    Require Import List.
    Import ListNotations.

    Definition divide arg := match arg with
                             | [[a;b]] => vbits [false;a]
                             | _ => vtt
                             end.
    Definition even arg := match arg with
                           | [[a;false]] => vbits [true]
                           | [[a;true]] => vbits [false]
                           | _ => vtt
                           end.
    Definition odd arg := match arg with
                           | [[a;false]] => vbits [false]
                           | [[a;true]] => vbits [true]
                           | _ => vtt
                          end.
    Definition threeNPlusOne arg := match arg with (* Fake implementation *)
                             | [[a;b]] => vbits [b;false]
                             | _ => vtt
                             end.



End Functions.
(* Do not open List scope as we define a joli bind *)


Section Example1.
  Definition r := 0.
  Definition InitReg := putenv env_nil r (cons true (cons false nil)).
  Inductive Extfuns := Even | Odd | Divide | ThreeNPlusOne | Register (idx: nat).

  Scheme Equality for Extfuns.
  Definition SigmaEnv : Env Extfuns ExternalFunction := EqEnv Extfuns_eq_dec.

  Axiom magic : forall {A},A .
  Definition sigma : (SigmaEnv.(env_t)).
    refine (putenv _ Divide {| sig := {| argSizes := cons 2 nil;
                                         retType := bit_t 2 |};
                               impl := divide|}).
    refine (putenv _ ThreeNPlusOne {| sig := {| argSizes := cons 2 nil;
                                                retType := bit_t 2 |};
                                      impl := threeNPlusOne |}).
    refine (putenv _ Even {| sig := {| argSizes := cons 2 nil;
                                       retType := bit_t 1 |};
                             impl := even|}).
    refine (putenv _ Odd {| sig := {| argSizes := cons 2 nil;
                                      retType := bit_t 1 |};
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
                                         retType := bit_t 2 |};
                               impl := divide_abst|}).
    refine (putenv _ ThreeNPlusOne {| sig := {| argSizes := cons 2 nil;
                                                retType := bit_t 2 |};
                                      impl := threeNPlusOne |}).
    refine (putenv _ Even {| sig := {| argSizes := cons 2 nil;
                                       retType := bit_t 1 |};
                             impl := even|}).
    refine (putenv _ Odd {| sig := {| argSizes := cons 2 nil;
                                      retType := bit_t 1 |};
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
