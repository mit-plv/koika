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
