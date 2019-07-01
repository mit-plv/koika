Inductive syntax {Var} :=
| Bind (var: Var) (expr: syntax) (body: syntax)
| Ref (var: Var)
| PureUnit
| PureBits (bits: list bool)
| If (cond: syntax) (tbranch: syntax) (fbranch: syntax)
| Fail
| Read (level: bool) (idx: nat) (offset: syntax)
| Write (level: bool) (idx: nat) (offset: syntax) (value: syntax)
| Call (idx: nat) (args: list syntax).
