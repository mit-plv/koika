(*! Frontend | Top-level module imported by Kôika programs !*)
Require Export
        Koika.SyntaxMacros
        Koika.Desugaring
        Koika.TypeInference
        Koika.TypedSemantics
        Koika.CircuitOptimization
        Koika.CircuitGeneration
        Koika.Primitives
        Koika.SyntaxFunctions
        Koika.TypedSyntaxFunctions
        Koika.Interop
        Koika.Parsing
        Koika.DeriveShow
        Koika.ExtractionSetup.

Notation compile_scheduler :=
  (compile_scheduler opt_constprop).

Class DummyPos pos_t := { dummy_pos: pos_t }.
Instance DummyPos_path : DummyPos path := {| dummy_pos := PThis |}.
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
Notation action := (action pos_t var_t fn_name_t).
Notation rule := (rule pos_t var_t fn_name_t).

Notation scheduler := (scheduler pos_t _).

Notation UInternalFunction reg_t ext_fn_t := (InternalFunction var_t fn_name_t (uaction reg_t ext_fn_t)).
Notation InternalFunction R Sigma sig tau := (InternalFunction var_t fn_name_t (action R Sigma sig tau)).

Notation register_update_circuitry R Sigma := (register_update_circuitry _ R Sigma ContextEnv).

Ltac eval_cbn x :=
  eval cbn in x.

Ltac eval_hnf x :=
  eval hnf in x.

Ltac eval_cbv x :=
  eval cbv in x.

Ltac eval_vm_compute x :=
  eval vm_compute in x.

Ltac eval_native_compute x :=
  eval native_compute in x.

Ltac tc_eval x :=
  eval_vm_compute x.

Ltac tc_eval_body x :=
  let t := type of x in
  let x := tc_eval x in
  constr:(x: t).

Declare Scope error_messages.
Notation ">>> x <<<" :=
  (UError {| epos := tt;
             emsg := ExplicitErrorInAst;
             esource := ErrSrc (ErrorHere x) |}) : error_messages.
Global Open Scope error_messages.

Notation desugar_and_tc_action R Sigma uaction :=
  (let desugared := desugar_action dummy_pos uaction in
   type_action R Sigma dummy_pos List.nil desugared).

Definition is_success {S F} (r: result S F) :=
  match r with
  | Success s => true
  | Failure f => false
  end.

Definition extract_success {S F} (r: result S F) (pr: is_success r = true) :=
  match r return is_success r = true -> S with
  | Success s => fun _ => s
  | Failure f => fun pr => match Bool.diff_false_true pr with end
  end pr.

Notation _must_succeed r :=
  (extract_success r (@eq_refl bool true <: is_success r = true)).

Ltac _tc_action_fast R Sigma uaction :=
  let result := constr:(desugar_and_tc_action R Sigma uaction) in
  let typed := constr:(projT2 (_must_succeed result)) in
  exact typed.

Arguments place_error_beacon {var_t fn_name_t reg_t ext_fn_t} / rev_target current_path a : assert.

Ltac _report_typechecking_errors uaction tc_result :=
  let tc_result := tc_eval_body tc_result in
  lazymatch tc_result with
  | Success _ =>
    fail "No error in this program"
  | Failure {| epos := ?path; emsg := ?err; esource := ErrSrc ?src |} =>
    let err := lazymatch err with
              | BasicError ?err => err
              | ?err => err
              end in
    let revpath := constr:(rev_path PThis path) in
    let beacon_ctx := constr:(place_error_beacon revpath PThis uaction) in
    let beacon_ctx := eval cbn in beacon_ctx in
    lazymatch beacon_ctx with
    | ([], _) =>
    fail "
## In term:
  " src "

## Type error:
  " err "

## Context unknown; please report this bug"
    | ([ErrorHere ?beacon], ?context) =>
    fail "
## In term:
  " beacon "

## Type error:
  " err "

## Context:
  " context
    | (_, ?context) =>
    fail "
## Type error:
  " err "

## Context:
  " context
    end
  | _ =>
    fail "Unexpected typechecker output:" tc_result
  end.

Ltac _tc_illtyped_action R Sigma uaction :=
  let annotated := constr:(reposition PThis uaction) in
  let result := constr:(desugar_and_tc_action R Sigma annotated) in
  _report_typechecking_errors uaction result.

Ltac _tc_action R Sigma uaction :=
  (_tc_action_fast R Sigma uaction ||
   _tc_illtyped_action R Sigma uaction).

Definition annotate_uaction_type {reg_t ext_fn_t}
           (R: reg_t -> type) (Sigma: ext_fn_t -> Sig 1)
           (ua: uaction reg_t ext_fn_t) :=
  ua : uaction reg_t ext_fn_t.

Ltac _arg_type R :=
  match type of R with
  | ?t -> _ => t
  end.

(* FIXME: Find a way to propagate reg_t and ext_fn_t from R and Sigma to ua.
   With this users could write [tc_action R Sigma {{ skip }}] directly, without
   having to annotate the [{{ skip }}]. *)
Notation tc_action R Sigma ua :=
  (ltac:(_tc_action R Sigma ua)) (only parsing).

Ltac _tc_rules R Sigma uactions :=
  let rule_name_t := _arg_type uactions in
  let res := constr:(fun r: rule_name_t =>
                      ltac:(destruct r eqn:? ;
                            lazymatch goal with
                            | [ H: _ = ?rr |- _ ] =>
                              (* FIXME: why does the ‘<:’ above need this hnf? *)
                              let ua := constr:(uactions rr) in
                              let ua := (eval hnf in ua) in
                              _tc_action R Sigma ua
                            end)) in
  exact res.

Notation tc_rules R Sigma actions :=
  (ltac:(_tc_rules R Sigma actions)) (only parsing).

Notation tc_compute t :=
  ltac:(let t := tc_eval_body t in
        exact t) (only parsing).
