Require Import SGA.Common SGA.Syntax SGA.Environments.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Instance EqEnv {K V: Type} (eqdec: forall k k': K, {k = k'} + {k <> k'}) : Env K V.
Proof.
  refine ({| env_t := list (K * V);
             env_nil := nil;
             getenv e k :=
               match List.find (fun '(k', v) => if eqdec k k' then true else false) e with
               | Some (_, v) => Some v
               | None => None
               end;
             putenv e k v := (k, v) :: e |}); intros.
  - abstract (reflexivity).
  - abstract (cbn; destruct eqdec; congruence).
  - abstract (cbn; destruct eqdec; congruence).
  - abstract (cbn; destruct eqdec; subst; split;
              intuition; repeat cleanup_step; eauto; congruence).
  - abstract (cbn; destruct eqdec; subst; split;
              intuition; repeat cleanup_step; eauto; congruence).
Defined.

Scheme Equality for string.
Instance StringEnv (V: Type) : Env string V := EqEnv string_eq_dec.
Instance NatEnv (V: Type) : Env nat V := EqEnv PeanoNat.Nat.eq_dec.

Inductive circuit {TSpecial: Type} : Type :=
| CQuestionMark
| CNot (c: circuit)
| CAnd (c1 c2: circuit)
| COr (c1 c2: circuit)
| CMux (select c1 c2: circuit)
| CConst (cst: bits)
| Special (s: TSpecial).
Arguments circuit: clear implicits.

Notation "$ c" := (CConst c) (at level 75) : circuit.
Notation "~ c" := (CNot c) (at level 75, right associativity) : circuit.
Notation "c1 && c2" := (CAnd c1 c2) (at level 40, left associativity) : circuit.
Notation "c1 || c2" := (COr c1 c2) (at level 50, left associativity) : circuit.
Notation "s ?? c1 // c2" := (CMux s c1 c2) (at level 80, no associativity) : circuit.
Open Scope circuit.

Record compiled_rule {T} :=
  { canFire: circuit T;
    read0: circuit T;
    read1: circuit T;
    write0: circuit T;
    write1: circuit T;
    data0: circuit T;
    data1: circuit T;
    retVal: circuit T }.
Arguments compiled_rule: clear implicits.

Record compiled_scheduler {T} :=
  { sread0: circuit T;
    sread1: circuit T;
    swrite0: circuit T;
    swrite1: circuit T;
    sdata0: circuit T;
    sdata1: circuit T }.
Arguments compiled_scheduler: clear implicits.

Section CircuitCompilation.
  Context {TSpecial: Type}.
  Context {TVar TFn: Type}.

  Notation circuit := (circuit TSpecial).
  Notation compiled_rule := (compiled_rule TSpecial).
  Notation compiled_scheduler := (compiled_scheduler TSpecial).

  Context {RegEnv: Env nat circuit}.
  Context {GammaEnv: Env TVar circuit}. (* Tracks only retvals *)
  Context {SigmaEnv: Env TFn (list circuit -> circuit)}.

  Context (Sigma: SigmaEnv.(env_t)).
  Context (V: RegEnv.(env_t)).

  Fixpoint compile_rule
           (Gamma: GammaEnv.(env_t))
           (r: rule TVar TFn)
           (input: compiled_rule):
    option compiled_rule :=
    match r with
    | Bind var expr body =>
      opt_bind (compile_rule Gamma expr input) (fun cExpr =>
      opt_bind (compile_rule (putenv Gamma var cExpr.(retVal)) body cExpr) (fun cBody =>
      Some cBody)) (* FIXME merge and apply L *)
    | Var var =>
      opt_bind (getenv Gamma var) (fun cVal =>
      Some {| retVal := cVal;
              (* Unchanged *)
              canFire := input.(canFire);
              read0 := input.(read0);
              read1 := input.(read1);
              write0 := input.(write0);
              write1 := input.(write1);
              data0 := input.(data0);
              data1 := input.(data1) |})
    | Skip =>
      Some {| retVal := $nil;
              (* Unchanged *)
              canFire := input.(canFire);
              read0 := input.(read0);
              read1 := input.(read1);
              write0 := input.(write0);
              write1 := input.(write1);
              data0 := input.(data0);
              data1 := input.(data1) |}
    | Const cst =>
      Some {| retVal := $cst;
              (* Unchanged *)
              canFire := input.(canFire);
              read0 := input.(read0);
              read1 := input.(read1);
              write0 := input.(write0);
              write1 := input.(write1);
              data0 := input.(data0);
              data1 := input.(data1) |}
    | If cond tbranch fbranch =>
      opt_bind (compile_rule Gamma cond input) (fun cCond =>
      opt_bind (compile_rule Gamma tbranch cCond) (fun cTbr =>
      opt_bind (compile_rule Gamma fbranch cCond) (fun cFbr =>
      Some {| canFire := cCond.(retVal) ?? cTbr.(canFire) // cTbr.(canFire);
              read0 := cCond.(retVal) ?? cTbr.(read0) // cFbr.(read0);
              read1 := cCond.(retVal) ?? cTbr.(read1) // cFbr.(read1);
              write0 := cCond.(retVal) ?? cTbr.(write0) // cFbr.(write0);
              write1 := cCond.(retVal) ?? cTbr.(write1) // cFbr.(write1);
              data0 := cCond.(retVal) ?? cTbr.(data0) // cFbr.(data0);
              data1 := cCond.(retVal) ?? cTbr.(data1) // cFbr.(data1);
              retVal := cCond.(retVal) ?? cTbr.(retVal) // cFbr.(retVal); |})))
    | Fail =>
      Some {| canFire := $[false];
              (* Unchanged *)
              read0 := input.(read0);
              read1 := input.(read1);
              write0 := input.(write0);
              write1 := input.(write1);
              data0 := input.(data0);
              data1 := input.(data1);
              retVal := input.(retVal) |}
    | Read P0 idx =>
      opt_bind (getenv V idx) (fun v =>
      Some {| canFire := input.(canFire) && ~ input.(read1) && ~ input.(write1);
              retVal := v;
              read0 := $[true];
              (* Unchanged *)
              read1 := input.(read1);
              write0 := input.(write0);
              write1 := input.(write1);
              data0 := input.(data0);
              data1 := input.(data1) |})
    | Read P1 idx =>
      opt_bind (getenv V idx) (fun v =>
      Some {| canFire := input.(canFire);
              retVal := input.(write0) ?? input.(data0) // v;
              read1 := $[true];
              (* Unchanged *)
              read0 := input.(read0);
              write0 := input.(write0);
              write1 := input.(write1);
              data0 := input.(data0);
              data1 := input.(data1) |})
    | Write P0 idx val =>
      opt_bind (compile_rule Gamma val input) (fun cVal =>
      Some {| canFire := input.(canFire) && ~ cVal.(read1) &&  ~ cVal.(write0) &&  ~ cVal.(write1);
              retVal := $[];
              write0 := $[true];
              data0 := input.(retVal);
              (* Unchanged *)
              read0 := input.(read0);
              read1 := input.(read1);
              write1 := input.(write1);
              data1 := input.(data1) |})
    | Write P1 idx val =>
      opt_bind (compile_rule Gamma val input) (fun cVal =>
      Some {| canFire := input.(canFire) && ~ cVal.(write1);
              retVal := $[];
              write1 := $[true];
              data1 := input.(retVal);
              (* Unchanged *)
              read0 := input.(read0);
              read1 := input.(read1);
              write0 := input.(write0);
              data0 := input.(data0) |})
    | Call idx args =>
      opt_bind (getenv Sigma idx) (fun cFn =>
      opt_bind (List.fold_left (fun acc arg =>
                                  opt_bind acc (fun '(input, cArgs) =>
                                  opt_bind (compile_rule Gamma arg input) (fun cArg =>
                                  Some (cArg, cArg.(retVal) :: cArgs))))
                               args (Some (input, []))) (fun '(input, cArgs) =>
      Some {| retVal := cFn cArgs;
              (* Unchanged *)
              canFire := input.(canFire);
              read0 := input.(read0);
              read1 := input.(read1);
              write0 := input.(write0);
              write1 := input.(write1);
              data0 := input.(data0);
              data1 := input.(data1) |}))
    end.

  Definition adapter (cs: compiled_scheduler) : compiled_rule :=
    {| retVal := CQuestionMark;
       canFire := $[true];
       data0 := cs.(sdata0);
       data1 := cs.(sdata1);
       read0 := $[false];
       read1 := $[false];
       write0 := $[false];
       write1 := $[false] |}.

  Fixpoint compile_scheduler
           (s: scheduler TVar TFn)
           (input: compiled_scheduler):
    option compiled_scheduler :=
    match s with
    | Done =>
      Some input
    | Try r st sf =>
      opt_bind (compile_rule env_nil r (adapter input)) (fun cRule =>
      let acc := {| sread0 := cRule.(read0) || input.(sread0);
                   sread1 := cRule.(read1) || input.(sread1);
                   swrite0 := cRule.(write0) || input.(swrite0);
                   swrite1 := cRule.(write1) || input.(swrite1);
                   sdata0 := cRule.(data0);
                   sdata1 := cRule.(data1) |} in
      opt_bind (compile_scheduler st acc) (fun cSt =>
      opt_bind (compile_scheduler sf input) (fun cSf =>
      let will_fire := CQuestionMark in
      Some {| sread0 := will_fire ?? cSt.(sread0) // cSf.(sread0);
              sread1 := will_fire ?? cSt.(sread1) // cSf.(sread1);
              swrite0 := will_fire ?? cSt.(swrite0) // cSf.(swrite0);
              swrite1 := will_fire ?? cSt.(swrite1) // cSf.(swrite1);
              sdata0 := will_fire ?? cSt.(sdata0) // cSf.(sdata0);
              sdata1 := will_fire ?? cSt.(sdata1) // cSf.(sdata1) |})))
    end.
End CircuitCompilation.

Section T.
  Open Scope string_scope.
  Example testprog : rule string string :=
    (Bind "x" (Read P0 0)
          (If (Call "even" [Var "x"])
              (Write P0 0 (Const [false; true]))
              (Write P0 0 (Const [true; false])))).

  Inductive specials :=
  | Even (bs: list (circuit specials))
  | Input (field: string)
  | ReadReg (idx: nat).

  Notation circuit := (circuit specials).
  Notation compiled_rule := (compiled_rule specials).

  Definition regenv : (NatEnv circuit).(env_t) :=
    putenv env_nil 0 (Special (ReadReg 0)).

  Definition fnenv : (StringEnv (list circuit -> circuit)).(env_t) :=
    putenv env_nil "even" (fun args => Special (Even args): circuit).

  Definition input :=
    adapter {| canFire := Special (Input "canFire");
               retVal := Special (Input "retVal");
               write1 := Special (Input "write1");
               data1 := Special (Input "data1");
               read0 := Special (Input "read0");
               read1 := Special (Input "read1");
               write0 := Special (Input "write0");
               data0 := Special (Input "data0") |}.

  Compute (compile_rule fnenv regenv env_nil testprog input).
