Inductive Level :=
  P0 | P1.

Notation bits := (list bool).

Inductive rule {TVar TFn} :=
| Bind (var: TVar) (expr: rule) (body: rule)
| Var (var: TVar)
| Skip
| Const (cst: bits)
| If (cond: rule) (tbranch: rule) (fbranch: rule)
| Fail
| Read (level: Level) (idx: nat)
| Write (level: Level) (idx: nat) (value: rule)
| Call (fn: TFn) (args: list rule).

Arguments rule : clear implicits.

Inductive scheduler {TVar TFn} :=
| Done
| Try (r: rule TVar TFn) (s1 s2: scheduler).

Arguments scheduler : clear implicits.

Require Import List.

(* Better induction principle *)
Definition rule_ind' {TVar TFn : Type} (P : rule TVar TFn -> Prop)
           (f : forall (var : TVar) (expr : rule TVar TFn),
               P expr -> forall body : rule TVar TFn, P body -> P (Bind var expr body))
           (f0 : forall var : TVar, P (Var var)) (f1 : P Skip) (f2 : forall cst : bits, P (Const cst))
           (f3 : forall cond : rule TVar TFn,
               P cond ->
               forall tbranch : rule TVar TFn,
                 P tbranch -> forall fbranch : rule TVar TFn, P fbranch -> P (If cond tbranch fbranch))
           (f4 : P Fail) (f5 : forall (level : Level) (idx : nat), P (Read level idx))
           (f6 : forall (level : Level) (idx : nat) (value : rule TVar TFn), P value -> P (Write level idx value))
           (f7: forall (fn : TFn) (args : list (rule TVar TFn)),
               List.Forall P args ->
               P (Call fn args)) : forall r, P r.
  refine (fix F (r : rule TVar TFn) : P r :=
            match r as r0 return (P r0) with
            | Bind var expr body => f var expr (F expr) body (F body)
            | Var var => f0 var
            | Skip => f1
            | Const cst => f2 cst
            | If cond tbranch fbranch => f3 cond (F cond) tbranch (F tbranch) fbranch (F fbranch)
            | Fail => f4
            | Read level idx => f5 level idx
            | Write level idx value => f6 level idx value (F value)
            | Call fn args => f7 fn args _
            end).
  revert args.
  fix fargs 1.
  destruct args; cbn; econstructor; eauto.
Defined.
