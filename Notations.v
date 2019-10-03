Require Export
        SGA.Common
        SGA.Syntax
        SGA.SyntaxMacros
        SGA.TypeInference
        SGA.Semantics
        SGA.Circuits
        SGA.Primitives
        SGA.Interop
        SGA.CircuitElaboration.

Delimit Scope sga_scope with sga.
Delimit Scope sga_expr_scope with sga_expr.

(* These are just for pattern-matching, since '~' doesn't work in matches *)
Notation "'Ob'" := (vect_nil) (at level 7, left associativity, only parsing) : bitparsing.
Notation "bs '~' 0" := {| vhd := false; vtl := bs |} (at level 7, left associativity, only parsing) : bitparsing.
Notation "bs '~' 1" := {| vhd := true; vtl := bs |} (at level 7, left associativity, only parsing) : bitparsing.
Notation "bs '~' b" := {| vhd := b; vtl := bs |} (at level 7, left associativity, only parsing) : bitparsing.
Delimit Scope bitparsing with bitparsing.
Notation "`` bs" := (bs%bitparsing) (only parsing, at level 6).

Notation "'Ob'" := (@vect_nil bool) (at level 7, left associativity, only printing) : bits_printing.
(* Notation "bs '~' b" := {| vhd := b; vtl := bs |} (at level 7, left associativity, only printing) : bits_printing. (* FIXME *) *)
Notation "bs '~' 0" := {| vhd := false; vtl := bs |} (at level 7, left associativity, only printing) : bits_printing.
Notation "bs '~' 1" := {| vhd := true; vtl := bs |} (at level 7, left associativity, only printing) : bits_printing.
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
  (UCall (UCustomFn f) arg (UConstBits Ob))
    (at level 99, arg at level 99, format "f [ arg ]") : sga_expr_scope.
Notation "f [ arg1 ',' arg2 ]" :=
  (UCall (UCustomFn f) arg1 arg2)
    (at level 99, arg1 at level 99, arg2 at level 99,
    format "f [ arg1 ','  arg2 ]") : sga_expr_scope.
Notation "f [[ arg ]]" :=
  (UCall (UPrimFn (UBitsFn f)) arg (UConstBits Ob))
    (at level 99, arg at level 99, format "f [[ arg ]]") : sga_expr_scope.
Notation "f [[ arg1 ',' arg2 ]]" :=
  (UCall (UPrimFn (UBitsFn f)) arg1 arg2)
    (at level 99, arg1 at level 99, arg2 at level 99,
    format "f [[ arg1 ','  arg2 ]]") : sga_expr_scope.

Notation "'skip'" :=
  (UConstBits Ob) (at level 99) : sga_scope.
Notation "'fail'" :=
  (UFail (bits_t 0)) (at level 99) : sga_scope.
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
  (UCons r s)
    (at level 99, s at level 99, right associativity) : sga_scope.
Notation "'done'" :=
  UDone (at level 99) : sga_scope.

Arguments Var {var_t reg_t fn_t R Sigma sig} k {tau} {m} : assert.

Notation "'[[read0]]'" := (LE LogRead P0 tt) (only printing).
Notation "'[[read1]]'" := (LE LogRead P1 tt) (only printing).
Notation "'[[write0'  v ']]'" := (LE LogWrite P0 v) (only printing).
Notation "'[[write1'  v ']]'" := (LE LogWrite P1 v) (only printing).
