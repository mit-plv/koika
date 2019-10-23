Require Export
        SGA.Common
        SGA.Syntax
        SGA.SyntaxMacros
        SGA.Desugaring
        SGA.TypeInference
        SGA.Semantics
        SGA.Circuits
        SGA.Primitives
        SGA.Interop.

Export SigNotations.
Export PrimUntyped.

Class DummyPos pos_t := { dummy_pos: pos_t }.
Instance DummyPos_unit : DummyPos unit := {| dummy_pos := tt |}.

Declare Custom Entry koika.

Notation "'{$' e '$}'" := e (e custom koika at level 200, format "'{$' '[v' '/' e '/' ']' '$}'").
Notation "'fail'" :=
  (UFail (bits_t 0)) (in custom koika at level 20, format "'fail'").
Notation "'fail' t" :=
  (UFail (bits_t t)) (in custom koika at level 20, t constr at level 0 ,format "'fail' t").
Notation "'UError'" := (USugar UErrorInAst) (in custom koika at level 20).
Notation "'let' a ':=' b 'in' c" := (UBind a b c) (in custom koika at level 99, a constr at level 0, right associativity, format "'[v' 'let'  a  ':='  b  'in' '/' c ']'").
Notation "a ';' b" := (USeq a b) (in custom koika at level 30, format "'[v' a ';' '/' b ']'" ).
Notation "'set' a ':=' b" := (UAssign a b) (in custom koika at level 29, a constr at level 0, format "'set'  a  ':='  b").


Notation "'(' a ')'" := (a) (in custom koika at level 99, a custom koika at level 99, format "'[v' '(' a ')' ']'", only parsing).


Notation "a" := (UVar a) (in custom koika at level 0, a constr at level 0, format "'[' a ']'").

Notation "'read0' '(' reg ')' " := (URead P0 reg) (in custom koika at level 30, reg constr, format "'read0' '(' reg ')'").
Notation "'read1' '(' reg ')' " := (URead P1 reg) (in custom koika at level 30, reg constr, format "'read1' '(' reg ')'").
Notation "'write0' '(' reg ',' value ')'" :=
  (UWrite P0 reg value)
    (in custom koika at level 30, reg constr at level 13, format "'write0' '(' reg ',' value ')'").
Notation "'write1' '(' reg ',' value ')'" :=
  (UWrite P1 reg value)
    (in custom koika at level 30, reg constr at level 13, format "'write1' '(' reg ',' value ')'").

Notation "'if' a 'then' t 'else' f" := (UIf a t f) (in custom koika at level 30, right associativity, format "'[v' 'if'  a '/' 'then'  t '/' 'else'  f ']'").
Notation "'when' a 'then' t " := (UIf a t (UFail (bits_t 0))) (in custom koika at level 30, right associativity, format "'[v' 'when'  a '/' 'then'  t '/' ']'").

Notation "a '&&' b" :=  (UBinop (UBits2 UAnd) a b) (in custom koika at level 80,  right associativity, format "a  '&&'  b").
Notation "'!' a" := (UUnop (UBits1 UNot) a) (in custom koika at level 75, a custom koika at level 99, format "'!' a").
Notation "a '||' b" :=  (UBinop (UBits2 UOr) a b) (in custom koika at level 85, format "a  '||'  b").
Notation "a '+' b" :=  (UBinop (UBits2 UUIntPlus) a b) (in custom koika at level 85, format "a  '+'  b").
Notation "a '==' b" :=  (UBinop UEq a b) (in custom koika at level 79, format "a  '=='  b").
Notation "a '>>' b" :=  (UBinop (UBits2 ULsr) a b) (in custom koika at level 79, format "a  '>>'  b").
Notation "a '<<' b" :=  (UBinop (UBits2 ULsl) a b) (in custom koika at level 79, format "a  '<<'  b").
Notation "'{' a ',' b '}'" := (UBinop (UBits2 UConcat) a b) (in custom koika at level 99, format "'{' a ',' b '}'").
Notation "a '[' b ']'" := (UBinop (UBits2 USel) a b) (in custom koika at level 75, format "'[' a [ b ] ']'").
Notation "a '[' b ':+' c ']'" := (UBinop (UBits2 (UIndexedPart c)) a b) (in custom koika at level 75, c constr at level 0, format "'[' a [ b ':+' c ] ']'").
Notation "'`' a '`'" := ( a) (in custom koika at level 50, a constr at level 99).

Declare Custom Entry koika_types.

Notation " x ':' y " := (cons (prod_of_argsig {| arg_name := x%string; arg_type := y |}) nil) (in custom koika_types at level 60,x constr at level 12, y constr at level 12 ).
Notation "a ',' b" := (app a b)  (in custom koika_types at level 95, a custom koika_types , b custom koika_types, right associativity).


Notation "'function' name '(' args ')' ':' ret ':=' body" :=
  {| int_name := name%string;
     int_argspec := args;
     int_retType := ret;
     int_body := body |}
    (at level 99, name constr at level 0, args custom koika_types, ret constr at level 0, body custom koika at level 99, format "'[v' 'function'  name '(' args ')'  ':'  ret  ':=' '/' body ']'").

Notation "'function' name ':' ret ':=' body" :=
  {| int_name := name%string;
     int_argspec := nil;
     int_retType := ret;
    int_body := body |}
    (at level 99, name constr at level 0,  ret constr at level 0, body custom koika at level 99,  format "'[v' 'function'  name  ':'  ret  ':=' '/' body ']'" ).



Declare Custom Entry koika_args.

Notation "x" := (cons x nil) (in custom koika_args at level 60, x custom koika at level 99).
Notation "arg1 , arg2" := (app arg1 arg2) (in custom koika_args at level 13, arg1 custom koika_args, arg2 custom koika_args).


Notation "'call' instance method args" :=
  (UCallModule instance id method args)
      (in custom koika at level 99, instance constr at level 0, method constr at level 0, args custom koika_args at level 0).
Notation "'funcall' method args" :=
    (UInternalCall method args)
                                   (in custom koika at level 99, method constr at level 0, args custom koika_args at level 0).
Notation "'call0' instance method " :=
    (UCallModule instance id method nil)
                                   (in custom koika at level 98, instance constr at level 0, method constr at level 0).
Notation "'funcall0' method " :=
    (UInternalCall method nil)
                                   (in custom koika at level 98,  method constr at level 0).
Notation "'get' '(' t ',' f ')'" :=
  (UUnop (UStruct1 (UGetField f)) t)
    (in custom koika at level 30, t custom koika at level 13, f constr at level 13, format "'get' '(' t ','  f ')'").

Notation "'#' s" := (UConstBits s) (in custom koika at level 98, s constr at level 0 ).


Notation "r '|>' s" :=
  (UCons r s)
    (at level 99, s at level 99, right associativity).
Notation "'done'" :=
  UDone (at level 99).

Module Type Tests.
  Parameter pos_t : Type.
  Parameter fn_name_t : Type.
  Parameter reg_t : Type.
  Parameter ext_fn_t : Type.
  Notation uaction reg_t := (uaction pos_t string fn_name_t reg_t ext_fn_t).
  Definition test_1 : uaction reg_t := {$ let "yoyo" := fail 2 in UError $}.
  Definition test_2 : uaction reg_t := {$ UError; UError $}.
  Definition test_3 : uaction reg_t := {$ set "yoyo" := UError ; UError $}.
  Definition test_4 : uaction reg_t := {$ UError ; set "yoyo" := UError $}.
  Definition test_5 : uaction reg_t := {$ let "yoyo" := set "yoyo" := UError in UError $}.
  Definition test_6 : uaction reg_t := {$ let "yoyo" := set "yoyo" := UError; UError in UError;UError $}.
  Definition test_7 : uaction reg_t := {$ (let "yoyo" := (set "yoyo" := UError); UError in UError;UError) $}.
  Definition test_8 : uaction reg_t := {$ (let "yoyo" := set "yoyo" := UError; UError in UError);UError $}.
  Inductive test : Set := |rData (n:nat).
  Axiom data0 : reg_t.
  Axiom data1 : reg_t.
  Definition test_9 : uaction reg_t := {$ read0(data0) $}.
  Definition test_10 : nat -> uaction test := (fun idx => {$ read0(rData idx) $}).
  Definition test_11 : uaction reg_t := {$ (let "yoyo" := read0(data0) in write0(data0, UError)); fail $}.
  Definition test_12 : uaction reg_t := {$ (let "yoyo" := if fail then read0(data0) else fail in write0(data0,UError));fail $}.
  Definition test_13 : uaction reg_t := {$ "yoyo" $}.
  Definition test_14 : uaction reg_t := {$ !"yoyo" && "yoyo" $}.
  Definition test_14' : uaction reg_t := {$ !("yoyo" && "yoyo") $}.
  Definition test_15 : uaction reg_t := {$ "yoyo" && read0(data0) $}.
  Definition test_16 : uaction reg_t := {$ !read0(data1) && !read0(data1) $}.
  Definition test_17 : uaction reg_t := {$ !read0(data1) && UError$}.
  Definition test_18 : uaction reg_t := {$ !read0(data1) && "Yoyo" $}.
  Definition test_19 : uaction reg_t := {$ "yoy" [ "oio" && "ab" ] && `UConstBits Ob~1~0` $}.
  Definition test_20 : uaction reg_t := {$ "yoyo" [ UError :+ 3 ] && "yoyo" $}.
  (* Notation "'{&' a '&}'" := (a) (a custom koika_types at level 200). *)
  (* Definition test_21 := {& "yoyo" : bits_t 2 &}. *)
  (* Definition test_22 := {& "yoyo" : bits_t 2 , "yoyo" : bits_t 2  &}. *)
  Definition test_23 : InternalFunction string string (uaction reg_t) := function "foo" ("arg1" : (bits_t 3),  "arg2" : (bits_t 2) ) :  bits_t 4 := UError.
  Definition test_24 : nat -> InternalFunction string string (uaction reg_t) := (fun sz => function "uouo" ("arg1" : bits_t sz , "arg1" : bits_t sz ) : bits_t sz  := UError).
  Definition test_25 : nat -> InternalFunction string string (uaction reg_t) := (fun sz => function "uouo" ("arg1" : bits_t sz ) : bits_t sz  := let "oo" := UError >> UError in UError).
  Definition test_26 : nat -> InternalFunction string string (uaction reg_t) := (fun sz => function "uouo" : bits_t sz  := UError).
  Definition test_27 : uaction reg_t := {$
           (if (!read0(data0)) then
              write0(data0, `UConstBits Ob~1`);
                let "yo" := if ("dlk" == `UConstBits Ob~1` ) then "bla" else "yoyo" || "foo"
                in
                write0(data0,`UConstBits Ob~1`)
            else
              read0(data0));
         fail
           $}.
  (* Notation "'{*' a '*}'" := (a) (a custom koika_args at level 200). *)
  (* Definition test_28 : list (uaction reg_t) := {* "yoyo" *}. *)
  (* Definition test_29 : list (uaction reg_t) := {* "yoyo", if "var" then UError else UError;UError *}. *)
End Tests.

Notation "'[[read0]]'" := (LE LogRead P0 tt) (only printing).
Notation "'[[read1]]'" := (LE LogRead P1 tt) (only printing).
Notation "'[[write0'  v ']]'" := (LE LogWrite P0 v) (only printing).
Notation "'[[write1'  v ']]'" := (LE LogWrite P1 v) (only printing).

Ltac __must_typecheck_extract_result x :=
  lazymatch x with
  | Success ?tm => tm
  | Failure {| epos := _; emsg := ?err; esource := ErrSrc ?src |} =>
    let err := match err with
              | BasicError ?err => err
              | ?err => err
              end in
    fail "Type error:" err "in term" src
  end.

Ltac __must_typecheck_cbn tcres :=
  let tcres := (eval hnf in tcres) in
  __must_typecheck_extract_result tcres.

(* This version is much faster, but it unfolds everything *)
Ltac __must_typecheck_vmc tcres :=
  let tcres := (eval vm_compute in tcres) in
  __must_typecheck_extract_result tcres.

Ltac __must_typecheck tcres :=
  __must_typecheck_vmc tcres.

Ltac _tc_action R Sigma action :=
  let desugared := constr:(desugar_action dummy_pos action) in
  let maybe_typed := constr:(type_action R Sigma dummy_pos List.nil desugared) in
  let typed := __must_typecheck maybe_typed in
  let typed := (eval cbn in (projT2 typed)) in
  exact typed.

Notation tc_action R Sigma action :=
  (ltac:(_tc_action R Sigma action)) (only parsing).

Ltac _tc_rules R Sigma actions :=
  lazymatch type of actions with
  | (?rule_name_t -> _) =>
    let res := constr:(fun r: rule_name_t =>
                        ltac:(destruct r eqn:? ;
                              lazymatch goal with
                              | [ H: _ = ?rr |- _ ] =>
                                _tc_action R Sigma (actions rr)
                              end)) in
    let res := (eval cbn in res) in
    exact res
  end.

Notation tc_rules R Sigma actions :=
  (ltac:(_tc_rules R Sigma actions)) (only parsing).

Notation tc_scheduler uscheduler :=
  (type_scheduler dummy_pos uscheduler) (only parsing).
