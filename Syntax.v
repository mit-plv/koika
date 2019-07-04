Inductive Level :=
  P0 | P1.

Notation bits := (list bool).

Inductive syntax {TVar TFn} :=
| Bind (var: TVar) (expr: syntax) (body: syntax)
| Var (var: TVar)
| Skip
| Const (cst: bits)
| If (cond: syntax) (tbranch: syntax) (fbranch: syntax)
| Fail
| Read (level: Level) (idx: nat)
| Write (level: Level) (idx: nat) (value: syntax)
| Call (fn: TFn) (args: list syntax).

Arguments syntax : clear implicits.