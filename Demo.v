Require Import SGA.Notations.
Require SGA.Primitives.

Require Import Coq.Strings.String.
Open Scope string_scope.

Definition readRegisters {reg_t fn_t: Type} (R: reg_t -> type) (Sigma: fn_t -> ExternalSignature)
  : forall idx: reg_t, circuit R Sigma (R idx) :=
  fun idx => CReadRegister (R := R) (Sigma := Sigma) idx.

Module Ex1.
  Notation var_t := string.
  Inductive reg_t := R0 | R1.
  Inductive fn_t := Even | Odd.

  Definition R reg : type :=
    match reg with
    | R0 => bits_t 3
    | R1 => bits_t 1
    end.

  Definition Sigma fn : ExternalSignature :=
    match fn with
    | Even => {{ 3 ~> 0 ~> 1}}
    | Odd => {{ 3 ~> 0 ~> 1}}
    end.

  Definition r idx : R idx :=
    match idx with
    | R0 => Ob~1~0~1
    | R1 => Ob~0
    end.

  Definition sigma idx : Sigma idx :=
    match idx with
    | Even => fun (bs: bits 3) _ => w1 (negb (Bits.lsb bs))
    | Odd => fun (bs: bits 3) _ => w1 (Bits.lsb bs)
    end.

  Example r1 : urule var_t reg_t fn_t :=
    (UBind "x" (URead P0 R0)
           (UIf (UCall Even (UVar "x") (UConst Ob))
                (UWrite P0 R1 (UConst Ob~1))
                (UWrite P0 R1 (UConst Ob~1)))).

  Example s1 : uscheduler var_t reg_t fn_t :=
    UTry r1 UDone UDone.

  Definition s1_result :=
    Eval compute in interp_scheduler (ContextEnv.(create) r) sigma (tc R Sigma s1).
  Definition s1_circuit :=
    compile_scheduler (ContextEnv.(create) (readRegisters R Sigma)) (tc R Sigma s1).
End Ex1.

Module Ex2.
  Definition var_t := string.
  Inductive reg_t := R0 | R1 | R2.
  Inductive fn_t := Or (n: nat) | Not (n: nat).

  Definition R r :=
    match r with
    | R0 => bits_t 7
    | R1 => bits_t 7
    | R2 => bits_t 1
    end.

  Definition Sigma fn :=
    match fn with
    | Or n => {{ n ~> n ~> n }}
    | Not n => {{ n ~> 0 ~> n }}
    end.

  Example negate : urule var_t reg_t fn_t  :=
    UBind "x" (URead P1 R0)
          (UWrite P1 R0 (UVar "x")).

  Example swap_or_replace : urule var_t reg_t fn_t  :=
    UBind "should_swap" (URead P0 R2)
          (UIf (UVar "should_swap")
               (USeq (UWrite P0 R1 (URead P0 R0))
                     (UWrite P0 R0 (URead P0 R1)))
               (UWrite P0 R0 (UCall (Or 7)
                                    (URead P0 R0)
                                    (URead P0 R1)))).

  Example ill_typed_write : urule var_t reg_t fn_t  :=
    UWrite P0 R2 (URead P0 R1).

  Example unbound_variable : urule var_t reg_t fn_t  :=
    UWrite P0 R0 (UVar "y").

  Example sched :=
    UTry swap_or_replace (UTry negate UDone UDone) (UTry negate UDone UDone).

  Example tsched : scheduler var_t R Sigma :=
    tc R Sigma sched.

  Fail Example tsched : scheduler var_t R Sigma :=
    must (type_scheduler R Sigma (UTry ill_typed_write UDone UDone)).

  Fail Example tsched : scheduler var_t R Sigma :=
    must (type_scheduler R Sigma (UTry unbound_variable UDone UDone)).

  Definition r idx : R idx :=
    match idx with
    | R0 => Ob~0~1~1~0~0~1~0
    | R1 => Ob~1~1~0~0~1~1~0
    | R2 => Ob~1
    end.

  Definition sigma idx : Sigma idx :=
    match idx with
    | Or n => fun bs1 bs2 => Bits.map2 orb bs1 bs2
    | Not n => fun bs _ => Bits.map negb bs
    end.

  Definition tsched_result :=
    Eval compute in interp_scheduler (ContextEnv.(create) r) sigma tsched.
  Definition tsched_circuit :=
    compile_scheduler (ContextEnv.(create) (readRegisters R Sigma)) tsched.
End Ex2.

Module Collatz.
  Definition var_t := string.
  Inductive reg_t := R0.
  Inductive custom_t := Divide | ThreeNPlusOne | Even | Odd.
  Definition fn_t := interop_fn_t custom_t.

  Definition R r :=
    match r with
    | R0 => bits_t 2
    end.

  Definition Sigma fn :=
    match fn with
    | Divide => {{ 2 ~> 0 ~> 2 }}
    | ThreeNPlusOne => {{ 2 ~> 0 ~> 2 }}
    | Even => {{ 2 ~> 0 ~> 1 }}
    | Odd => {{ 2 ~> 0 ~> 1 }}
    end.

  Definition r idx : R idx :=
    match idx with
    | R0 => Ob~1~0
    end.

  (* TODO bug report *)
  (* Notation "!!!!" := ltac:(exact (true, false, tt)). *)
  (* Compute match (true, true, tt) with *)
  (*         | !!!! => 1 *)
  (*         end. *)

  Definition sigma idx : Sigma idx :=
    match idx with
    | Divide => fun '(`` Ob~b1~b2) _ => Ob~0~b1
    | ThreeNPlusOne => fun bs _ => match bs with
                               | `` Ob~0~0 => Ob~0~1
                               | `` Ob~0~1 => Ob~0~0
                               | `` Ob~1~0 => Ob~1~1
                               | `` Ob~1~1 => Ob~1~0
                               end
    | Even => fun '(`` Ob~_~b2) _ => Ob~(negb b2)
    | Odd => fun '(`` Ob~_~b2) _ => Ob~b2
    end.

  Open Scope sga.

  Definition divide_collatz : urule var_t reg_t fn_t :=
    Let "v" <- R0#read0 in
    Let "odd" <- (Sel 1)[[$"v", UConst Ob~0]] in
    If (Not 1)[[$"odd"]] Then
       R0#write0(Divide[$"v"])
    Else
      fail
    EndIf.

  Definition multiply_collatz : urule var_t reg_t fn_t :=
    Let "v" <- R0#read1 in
    Let "odd" <- (Sel 1)[[$"v", UConst Ob~0]] in
    If $"odd" Then
        R0#write1(ThreeNPlusOne[$"v"])
    Else
       fail
    EndIf.

(* Bug report *)
(* Require Import Coq.extraction.Extraction. *)
(* (* Extraction Language JSON. *) *)
(* Set Extraction KeepSingleton. *)
(* Extraction Collatz.reg_t. *)

  (* Definition rl : rule var_t R Sigma List.nil := *)
  (*   tc R Sigma (Let "v" <- R0#read1 in *)
  (*           Let "y" <- (Or _)[[UConst Ob~1~1, UConst Ob~1~1]] in *)
  (*           If Odd[$"v"] Then *)
  (*               R0#write1(Divide[$"v"]) *)
  (*           Else *)
  (*              fail *)
  (*           EndIf). *)

  Definition iSigma := interop_Sigma Sigma.
  Definition isigma := interop_sigma sigma.
  Definition cr := ContextEnv.(create) r.

  Definition collatz : scheduler _ _ _ :=
    tc R iSigma (divide_collatz |> multiply_collatz |> done).

  Notation compute t :=
    ltac:(let tt := type of t in
          let t := (eval vm_compute in t) in
          exact (t: tt)) (only parsing).

  Open Scope bits_printing.
  Definition result :=
    compute (interp_scheduler cr isigma collatz).
  Definition divide_result :=
    compute (interp_rule cr isigma CtxEmpty log_empty log_empty
                         (tc R iSigma divide_collatz)).
  Definition multiply_result :=
    compute (interp_rule cr isigma CtxEmpty log_empty log_empty
                         (tc R iSigma multiply_collatz)).

  Definition circuit :=
    compile_scheduler (ContextEnv.(create) (readRegisters R iSigma)) collatz.

  Definition package :=
    {| vp_reg_t := reg_t;
       vp_reg_types := R;
       vp_reg_init := r;
       vp_reg_finite := _;
       vp_reg_Env := ContextEnv;

       vp_custom_fn_t := custom_t;
       vp_custom_fn_types := Sigma;

       vp_reg_names r := match r with
                        | R0 => "R0"
                        end;
       vp_custom_fn_names fn := match fn with
                               | Divide => "Divide"
                               | ThreeNPlusOne => "ThreeNPlusOne"
                               | Even => "Even"
                               | Odd => "Odd"
                               end;

       vp_circuit := circuit;
    |}.
End Collatz.
