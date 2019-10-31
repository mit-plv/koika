Require Export
        Koika.SyntaxMacros
        Koika.Desugaring
        Koika.TypeInference
        Koika.Semantics
        Koika.Circuits
        Koika.Primitives
        Koika.TypedSyntaxTools
        Koika.Interop
        Koika.Parsing.

Class DummyPos pos_t := { dummy_pos: pos_t }.
Instance DummyPos_unit : DummyPos unit := {| dummy_pos := tt |}.

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

Notation uaction := (uaction pos_t var_t fn_name_t).
Notation action := (action pos_t var_t).
Notation rule := (rule pos_t var_t).

Notation uscheduler := (uscheduler pos_t _).
Notation scheduler := (scheduler pos_t _).

Notation UInternalFunction reg_t ext_fn_t := (InternalFunction fn_name_t var_t (uaction reg_t ext_fn_t)).
Notation InternalFunction R Sigma sig tau := (InternalFunction fn_name_t var_t (action R Sigma sig tau)).

Notation register_update_circuitry R Sigma := (register_update_circuitry _ R Sigma ContextEnv).

Ltac eval_cbn x :=
  let x := (eval cbn in x) in constr:(x).

Ltac eval_hnf x :=
  let x := (eval hnf in x) in constr:(x).

Ltac eval_cvb x :=
  let x := (eval cbv in x) in constr:(x).

Ltac eval_vm_compute x :=
  let x := (eval vm_compute in x) in constr:(x).

Ltac eval_native_compute x :=
  let x := (eval native_compute in x) in constr:(x).

Ltac tc_eval x :=
  eval_vm_compute x.

Ltac tc_eval_body x :=
  let t := type of x in
  let x := tc_eval x in
  constr:(x: t).

Ltac _must_typecheck x :=
  let x := tc_eval_body x in
  lazymatch x with
  | Success ?tm => tm
  | Failure {| epos := _; emsg := ?err; esource := ErrSrc ?src |} =>
    let err := match err with
               | BasicError ?err => err
               | ?err => err
               end in
    fail "Type error:" err "in term" src
  | _ => fail "Unexpected term:" x
  end.

Ltac _tc_action R Sigma action :=
  let maybe_typed :=
      constr:(let desugared := desugar_action dummy_pos action in
              type_action R Sigma dummy_pos List.nil desugared) in
  let typed := _must_typecheck maybe_typed in
  let typed := tc_eval_body (projT2 typed) in
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
    let res := tc_eval_body res in
    exact res
  end.

Notation tc_rules R Sigma actions :=
  (ltac:(_tc_rules R Sigma actions)) (only parsing).

Notation tc_scheduler uscheduler :=
  (type_scheduler dummy_pos uscheduler) (only parsing).

Notation tc_compute t :=
  ltac:(let t := tc_eval_body t in
        exact t) (only parsing).
