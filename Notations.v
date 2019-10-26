Require Export
        SGA.Common
        SGA.Syntax
        SGA.SyntaxMacros
        SGA.Desugaring
        SGA.TypeInference
        SGA.Semantics
        SGA.Circuits
        SGA.Primitives
        SGA.Interop
        SGA.SyntaxTools.

Export SigNotations.
Export PrimUntyped.

Require Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import SGA.IdentParsing.
Export Coq.Lists.List.ListNotations.
Open Scope list_scope.
Open Scope string_scope.

Class DummyPos pos_t := { dummy_pos: pos_t }.
Instance DummyPos_unit : DummyPos unit := {| dummy_pos := tt |}.

Declare Custom Entry koika.

Notation "'{{' e '}}'" := (e) (e custom koika at level 200, format "'{{' '[v' '/' e '/' ']' '}}'").
Notation "'fail'" :=
  (UFail (bits_t 0)) (in custom koika, format "'fail'").
Notation "'fail' '(' t ')'" :=
  (UFail (bits_t t)) (in custom koika, t constr at level 0 ,format "'fail' '(' t ')'").

Notation "'True'" := (USugar (UConstBits Ob~1)) (in custom koika).
Notation "'False'" := (USugar (UConstBits Ob~1)) (in custom koika).
Notation "'magic'" := (USugar UErrorInAst) (in custom koika).

Declare Custom Entry koika_var.
Notation "a" := (ident_to_string a) (in custom koika_var at level 0, a constr at level 0, format "'[' a ']'",only parsing).
Notation "a" := (a) (in custom koika_var at level 0, a constr at level 0, format "'[' a ']'",only printing).

Notation "'let' a ':=' b 'in' c" := (UBind a b c) (in custom koika at level 99, a custom koika_var at level 0, right associativity, format "'[v' 'let'  a  ':='  b  'in' '/' c ']'").
Notation "a ';' b" := (USeq a b) (in custom koika at level 30, format "'[v' a ';' '/' b ']'" ).
Notation "'set' a ':=' b" := (UAssign a b) (in custom koika at level 29, a custom koika_var at level 0, format "'set'  a  ':='  b").


Notation "'(' a ')'" := (a) (in custom koika , a custom koika, format "'[v' '(' a ')' ']'").

Notation "a" := (UVar a) (in custom koika at level 0, a  custom koika_var at level 0).

Notation "'read0' '(' reg ')' " := (URead P0 reg) (in custom koika, reg constr, format "'read0' '(' reg ')'").
Notation "'read1' '(' reg ')' " := (URead P1 reg) (in custom koika, reg constr, format "'read1' '(' reg ')'").
Notation "'write0' '(' reg ',' value ')'" :=
  (UWrite P0 reg value)
    (in custom koika, reg constr at level 13, format "'write0' '(' reg ',' value ')'").
Notation "'write1' '(' reg ',' value ')'" :=
  (UWrite P1 reg value)
    (in custom koika, reg constr at level 13, format "'write1' '(' reg ',' value ')'").

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
Notation "'`' a '`'" := ( a) (in custom koika, a constr at level 99).

Declare Custom Entry koika_types.

Notation " x ':' y " := (cons (prod_of_argsig {| arg_name := x%string; arg_type := y |}) nil) (in custom koika_types at level 60,x custom koika_var at level 12, y constr at level 12 ).
Notation "a ',' b" := (app a b)  (in custom koika_types at level 95, a custom koika_types , b custom koika_types, right associativity).


Notation "'function' '(' args ')' ':' ret ':=' body" :=
  {| int_name := "";
     int_argspec := args;
     int_retType := ret;
     int_body := body |}
    (at level 99, args custom koika_types, ret constr at level 0, body custom koika at level 99, format "'[v' 'function' '(' args ')'  ':'  ret  ':=' '/' body ']'").

Notation "'function' ':' ret ':=' body" :=
  {| int_name := "";
     int_argspec := nil;
     int_retType := ret;
    int_body := body |}
    (at level 99, ret constr at level 0, body custom koika at level 99,  format "'[v' 'function'  ':'  ret  ':=' '/' body ']'" ).



Declare Custom Entry koika_args.

Notation "x" := (cons x nil) (in custom koika_args at level 60, x custom koika at level 99).
Notation "arg1 , arg2" := (app arg1 arg2) (in custom koika_args at level 13, arg1 custom koika_args, arg2 custom koika_args).
Notation "a '++' b" :=  (UBinop (UBits2 UConcat) a b) (in custom koika at level 80,  right associativity, format "a  '++'  b").
Notation "'call' instance method '(' args ')'" :=
    (UCallModule instance id method args)
      (in custom koika at level 99, instance constr at level 0, method constr at level 0, args custom koika_args at level 0).
Notation "'funcall' method '(' args ')'" :=
    (UInternalCall method args)
                                   (in custom koika, method constr at level 0, args custom koika_args at level 0).
Notation "'call0' instance method " :=
    (UCallModule instance id method nil)
                                   (in custom koika at level 98, instance constr at level 0, method constr at level 0).
Notation "'funcall0' method " :=
    (UInternalCall method nil)
                                   (in custom koika at level 98,  method constr at level 0).
Notation "'get' '(' t ',' f ')'" :=
  (UUnop (UStruct1 (UGetField f)) t)
    (in custom koika, t custom koika at level 13, f custom koika_var at level 13, format "'get' '(' t ','  f ')'").
Notation "'subst' '(' t ',' f ',' a ')'" :=
  (UBinop (UStruct2 (USubstField f)) t a)
    (in custom koika, t custom koika at level 13, a custom koika at level 13, f custom koika_var at level 13, format "'subst' '(' t ','  f ',' a ')'").

Declare Custom Entry koika_structs_init.


Notation "f ':=' expr" := (cons (f,expr) nil) (in custom koika_structs_init at level 60, f custom koika_var at level 0, expr custom koika at level 0).
Notation "a ';' b" := (app a b) (in custom koika_structs_init at level 99, a custom koika_structs_init).
Notation "'struct' structtype '{|' fields '|}'" :=
  (USugar (UStructInit structtype fields)) (in custom koika, structtype constr at level 0, fields custom koika_structs_init).

Notation "'enum' enum_type f" :=
  (USugar (UConstEnum enum_type f))
    (in custom koika at level 0, enum_type constr at level 0, f custom koika_var at level 0).




Declare Custom Entry koika_branches.

Notation "x '=>' a " := (cons (x,a) nil) (in custom koika_branches at level 60, x custom koika at level 99, a custom koika at level 99).
Notation "arg1 '|' arg2" := (app arg1 arg2) (in custom koika_branches at level 13, arg1 custom koika_args, arg2 custom koika_args, format "'[v' arg1 ']' '/' '|'  '[v' arg2 ']'").

Notation "'match' var 'with' '|' branches 'return' 'default' ':' default 'end'" :=
  (UBind "__reserved__matchPattern" var (USugar (USwitch (UVar "__reserved__matchPattern") default branches)))
    (in custom koika at level 30,
        var custom koika,
        branches custom koika_branches,
        default custom koika ,
        format "'match'  var  'with' '/' '[v'  '|'  branches '/' 'return'  'default' ':' default ']' 'end'").

Notation "'#' s" := (USugar (UConstBits s)) (in custom koika at level 98, s constr at level 0 ).


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
  Definition test_1 : uaction reg_t := {{ let yoyo := fail(2) in magic }}.
  Definition test_1' : uaction reg_t := {{ let yoyo := fail(2) in yoyo }}.
  Definition test_2 : uaction reg_t := {{ magic; magic }}.
  Definition test_3 : uaction reg_t := {{ set yoyo := magic ; magic }}.
  Definition test_4 : uaction reg_t := {{ magic ; set yoyo := magic }}.
  Definition test_5 : uaction reg_t := {{ let yoyo := set yoyo := magic in magic }}.
  Definition test_6 : uaction reg_t := {{ let yoyo := set yoyo := magic; magic in magic;magic }}.
  Definition test_7 : uaction reg_t := {{ (let yoyo := (set yoyo := magic); magic in magic;magic) }}.
  Definition test_8 : uaction reg_t := {{ (let yoyo := set yoyo := magic; magic in magic);magic }}.
  Inductive test : Set := |rData (n:nat).
  Axiom data0 : reg_t.
  Axiom data1 : reg_t.
  Definition test_9 : uaction reg_t := {{ read0(data0) }}.
  Definition test_10 : nat -> uaction test := (fun idx => {{ read0(rData idx) }}).
  Definition test_11 : uaction reg_t := {{ (let yoyo := read0(data0) in write0(data0, magic)); fail }}.
  Definition test_12 : uaction reg_t := {{ (let yoyo := if fail then read0(data0) else fail in write0(data0,magic));fail }}.
  Definition test_13 : uaction reg_t := {{ yoyo }}.
  Definition test_14 : uaction reg_t := {{ !yoyo && yoyo }}.
  Definition test_14' : uaction reg_t := {{ !(yoyo && yoyo) }}.
  Definition test_15 : uaction reg_t := {{ yoyo && read0(data0) }}.
  Definition test_16 : uaction reg_t := {{ !read0(data1) && !read0(data1) }}.
  Definition test_17 : uaction reg_t := {{ !read0(data1) && magic}}.
  Definition test_18 : uaction reg_t := {{ !read0(data1) && Yoyo }}.
  Definition test_19 : uaction reg_t := {{ yoy [ oio && ab ] && `UConstBits Ob~1~0` }}.
  Definition test_20 : uaction reg_t := {{ yoyo [ magic :+ 3 ] && yoyo }}.
  Definition test_20' : uaction reg_t := {{ {yoyo [ magic :+ 3 ], yoyo} && yoyo }}.
  Definition test_20'' : uaction reg_t := {{ { {yoyo [ magic :+ 3 ], yoyo},bla} && yoyo }}.

  (* Notation "'{&' a '&}'" := (a) (a custom koika_types at level 200). *)
  (* Definition test_21 := {& "yoyo" : bits_t 2 &}. *)
  (* Definition test_22 := {& "yoyo" : bits_t 2 , "yoyo" : bits_t 2  &}. *)
  Definition test_23 : InternalFunction string string (uaction reg_t) := function (arg1 : (bits_t 3),  arg2 : (bits_t 2) ) :  bits_t 4 := magic.
  Definition test_24 : nat -> InternalFunction string string (uaction reg_t) := (fun sz => function  (arg1 : bits_t sz , arg1 : bits_t sz ) : bits_t sz  := magic).
  Definition test_25 : nat -> InternalFunction string string (uaction reg_t) := (fun sz => function (arg1 : bits_t sz ) : bits_t sz  := let oo := magic >> magic in magic).
  Definition test_26 : nat -> InternalFunction string string (uaction reg_t) := (fun sz => function : bits_t sz  := magic).
  Definition test_27 : uaction reg_t :=
    {{
           (if (!read0(data0)) then
              write0(data0, `UConstBits Ob~1`);
                let yo := if (dlk == `UConstBits Ob~1` ) then bla else yoyo || foo
                in
                write0(data0,`UConstBits Ob~1`)
            else
              read0(data0));
         fail
    }}.
  Definition test_28 : uaction reg_t :=  {{
          match var with
          | magic => magic
          return default: magic
          end
      }}.

  Definition mem_req :=
    {| struct_name := "mem_req";
       struct_fields := cons ("type", bits_t 1)
                          nil |}.

  Definition test_30'' : uaction reg_t :=
    {{
          struct mem_req {| foo := (upu; foo) ; bar := magic |}
    }}.

  Definition test_29 : uaction reg_t :=
    {{
          struct mem_req {| foo := upu; bar := magic |}
    }}.

End Tests.

Declare Scope log_entries.
Notation "'read0'" := (LE LogRead P0 tt) (only printing) : log_entries.
Notation "'read1'" := (LE LogRead P1 tt) (only printing) : log_entries.
Notation "'write0' v" := (LE LogWrite P0 v) (at level 10, only printing) : log_entries.
Notation "'write1' v" := (LE LogWrite P1 v) (at level 10, only printing) : log_entries.

Declare Scope context.
Notation "∅" :=
  (CtxEmpty) (at level 80, only printing) : context.
Notation "[ x  ↦  y ]  ::  tl" :=
  (CtxCons x y tl) (at level 80, right associativity, only printing) : context.

(* FIXME *)
Declare Scope bits_printing.
Notation "'Ob'" :=
  (@_vect_nil bool)
    (at level 7, left associativity, only printing) : bits_printing.
Notation "bs '~' 0" :=
  {| vhd := false; vtl := bs |}
    (at level 7, left associativity, only printing) : bits_printing.
Notation "bs '~' 1" :=
  {| vhd := true; vtl := bs |}
    (at level 7, left associativity, only printing) : bits_printing.

Open Scope context.
Open Scope log_entries.
Open Scope bits_printing.

Definition pos_t := unit.
Definition var_t := string.
Definition fn_name_t := string.

Notation scheduler := (scheduler pos_t _).
Notation uaction := (uaction pos_t var_t fn_name_t).
Notation UInternalFunction reg_t ext_fn_t := (InternalFunction fn_name_t var_t (uaction reg_t ext_fn_t)).

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
