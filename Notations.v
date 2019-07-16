Require Export SGA.Common SGA.Syntax SGA.TypeInference SGA.Semantics SGA.Circuits SGA.Primitives.

Delimit Scope sga_scope with sga.
Delimit Scope sga_expr_scope with sga_expr.

(* These are just for pattern-matching, since '~' doesn't work in matches *)
Notation "'w0'" := (tt) (at level 5, right associativity, only parsing) : bitparsing.
Notation "0 '~' bs" := (false, bs) (at level 5, right associativity, only parsing) : bitparsing.
Notation "1 '~' bs" := (true, bs) (at level 5, right associativity, only parsing) : bitparsing.
Delimit Scope bitparsing with bitparsing.
Notation "`` bs" := (bs%bitparsing) (only parsing, at level 6).

Notation "'w0'" := (tt) (at level 5, right associativity, only printing) : bits_printing.
Notation "0 '~' bs" := (false, bs) (at level 5, right associativity, only printing) : bits_printing.
Notation "1 '~' bs" := (true, bs) (at level 5, right associativity, only printing) : bits_printing.
Global Open Scope bits_printing.

Notation "$ var" :=
  (UVar var)
    (at level 75, format "$ var") : sga_expr_scope.
Notation "reg '#read0'" :=
  (URead P0 reg)
    (at level 99, format "reg '#read0'") : sga_expr_scope.
Notation "reg '#read1'" :=
  (URead P1 reg)
    (at level 99, format "reg '#read1'") : sga_expr_scope.
Notation "f [ arg ]" :=
  (UCall (CustomFn f) arg (UConst w0))
    (at level 99, arg at level 99, format "f [ arg ]") : sga_expr_scope.
Notation "f [ arg1 ',' arg2 ]" :=
  (UCall (CustomFn f) arg1 arg2)
    (at level 99, arg1 at level 99, arg2 at level 99,
    format "f [ arg1 ','  arg2 ]") : sga_expr_scope.
Notation "f [[ arg ]]" :=
  (UCall (PrimFn f) arg (UConst w0))
    (at level 99, arg at level 99, format "f [[ arg ]]") : sga_expr_scope.
Notation "f [[ arg1 ',' arg2 ]]" :=
  (UCall (PrimFn f) arg1 arg2)
    (at level 99, arg1 at level 99, arg2 at level 99,
    format "f [[ arg1 ','  arg2 ]]") : sga_expr_scope.

Notation "'skip'" :=
  USkip (at level 99) : sga_scope.
Notation "'fail'" :=
  UFail (at level 99) : sga_scope.
Notation "r1 ';;' r2" :=
  (USeq r1 r2) (at level 99) : sga_scope.
Notation "'Let' var '<-' expr 'in' body" :=
  (UBind var expr%sga_expr body)
    (at level 99, body at level 98,
     format "'Let'  var  '<-'  expr  'in'  body") : sga_scope.
Notation "'If' c 'Then' tbr 'Else' fbr 'EndIf'" :=
  (UIf c%sga_expr tbr fbr) (at level 99) : sga_scope.
Notation "reg '#write0' value" :=
  (UWrite P0 reg value%sga_expr)
    (at level 99, format "reg '#write0'  value") : sga_scope.
Notation "reg '#write1' value" :=
  (UWrite P1 reg value%sga_expr)
    (at level 99, format "reg '#write1'  value") : sga_scope.

Notation "r '|>' s" :=
  (UTry r s s)
    (at level 99, s at level 99, right associativity) : sga_scope.
Notation "'done'" :=
  UDone (at level 99) : sga_scope.

Arguments Var {_ _ _ _ _ _} k {tau} {_}.

Notation "'[[read0]]'" := (LE LogRead P0 tt) (only printing).
Notation "'[[read1]]'" := (LE LogRead P1 tt) (only printing).
Notation "'[[write0'  v ']]'" := (LE LogWrite P0 v) (only printing).
Notation "'[[write1'  v ']]'" := (LE LogWrite P1 v) (only printing).
