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
        Koika.Compiler
        Koika.Parsing
        Koika.DeriveShow
        Koika.BitTactics
        Koika.ProgramTactics
        Koika.ExtractionSetup.

Notation compile_scheduler :=
  (compile_scheduler opt_constprop).

Notation lower_r := Lowering.lower_r.

Class DummyPos pos_t := { dummy_pos: pos_t }.
Instance DummyPos_path : DummyPos path := {| dummy_pos := PThis |}.
Instance DummyPos_unit : DummyPos unit := {| dummy_pos := tt |}.

Declare Scope log_entries.
Notation "'read0'" := (LE LogRead P0 tt) (only printing) : log_entries.
Notation "'read1'" := (LE LogRead P1 tt) (only printing) : log_entries.
Notation "'write0' v" := (LE LogWrite P0 v) (at level 10, only printing) : log_entries.
Notation "'write1' v" := (LE LogWrite P1 v) (at level 10, only printing) : log_entries.

Declare Scope context.
Declare Custom Entry context_mapping.

Notation "x  =>  y" :=
  (CtxCons x y CtxEmpty)
    (in custom context_mapping at level 80,
        x constr at level 0, y constr at level 80,
        no associativity).

Notation "x  =>  y ;  z" :=
  (CtxCons x y z)
    (in custom context_mapping at level 80,
        x constr at level 0, y constr at level 80,
        z custom context_mapping at level 80,
        right associativity).

Notation "#{  x  }#" := (x) (at level 0, x custom context_mapping at level 200) : context.

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

Notation desugar_and_tc_action R Sigma tau sig uaction :=
  (let desugared := desugar_action dummy_pos uaction in
   tc_action R Sigma dummy_pos tau sig desugared).

Notation desugar_and_tc_rule R Sigma uaction :=
  (let desugared := desugar_action dummy_pos uaction in
   tc_rule R Sigma dummy_pos desugared).

Notation _must_succeed_conv r :=
  (extract_success r (@eq_refl bool true : is_success r = true)).
Notation _must_succeed_vm r :=
  (extract_success r (@eq_refl bool true <: is_success r = true)).
Notation _must_succeed_native r :=
  (extract_success r (@eq_refl bool true <<: is_success r = true)).

Inductive TC_Strategy := TC_conv | TC_vm | TC_native.
Ltac _tc_strategy := exact TC_vm.

Ltac _extract_success r :=
  let strategy := constr:(ltac:(_tc_strategy)) in
  let eq_pr :=
      match strategy with
      | TC_conv => constr:(@eq_refl bool true : is_success r = true)
      | TC_vm => constr:(@eq_refl bool true <: is_success r = true)
      | TC_native => constr:(@eq_refl bool true <<: is_success r = true)
      end in
  exact (extract_success r eq_pr).

Ltac _tc_action_fast R Sigma sig tau uaction :=
  let result := constr:(desugar_and_tc_action R Sigma sig tau uaction) in
  _extract_success result.

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

Ltac _tc_illtyped_action R Sigma sig tau uaction :=
  let annotated := constr:(reposition PThis uaction) in
  let result := constr:(desugar_and_tc_action R Sigma sig tau annotated) in
  _report_typechecking_errors uaction result.

Ltac _tc_action R Sigma sig tau uaction :=
  (_tc_action_fast R Sigma sig tau uaction ||
   _tc_illtyped_action R Sigma sig tau uaction).

(* FIXME: Find a way to propagate reg_t and ext_fn_t from R and Sigma to ua.
   With this users could write [tc_action R Sigma {{ skip }}] directly, without
   having to annotate the [{{ skip }}]. *)
Notation tc_action R Sigma sig tau ua :=
  (ltac:(_tc_action R Sigma sig tau ua)) (only parsing).

Notation tc_rule R Sigma ua :=
  (tc_action R Sigma (@List.nil (var_t * type)) unit_t ua) (only parsing).

Notation tc_function R Sigma uf :=
  (tc_action R Sigma (int_argspec uf) (int_retSig uf) (int_body uf)) (only parsing).

Ltac _arg_type R :=
  match type of R with
  | ?t -> _ => t
  end.

Ltac _tc_rules R Sigma uactions :=
  let rule_name_t := _arg_type uactions in
  let res := constr:(fun r: rule_name_t =>
                      ltac:(destruct r eqn:? ;
                            lazymatch goal with
                            | [ H: _ = ?rr |- _ ] =>
                              (* FIXME: why does the ‘<:’ above need this hnf? *)
                              let ua := constr:(uactions rr) in
                              let ua := (eval hnf in ua) in
                              _tc_action R Sigma (@List.nil (var_t * type)) constr:(unit_t) ua
                            end)) in
  exact res.

Notation tc_rules R Sigma actions :=
  (ltac:(_tc_rules R Sigma actions)) (only parsing).

Notation tc_compute t :=
  ltac:(let t := tc_eval_body t in
        exact t) (only parsing).
