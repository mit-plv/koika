(*;;; Syntax and typing errors *)
Require Import Koika.Frontend.

Inductive reg_t := R0.
Inductive rule_name_t := .

Definition R r :=
  match r with
  | R0 => bits_t 1
  end.

(* FIXME add more examples of errors *)

Fail Example ill_typed_write :=
  let u := {{ write0(R0, Ob~1~0) }} in
  tc_action R empty_Sigma u.

Fail Example unbound_variable : uaction reg_t empty_ext_fn_t  :=
  let u := {{ write0(R0, y) }} in
  tc_action R empty_Sigma u.

Definition empty_scheduler : TypedSyntax.scheduler pos_t rule_name_t :=
  tc_scheduler (done).

Definition r idx : R idx :=
  match idx with
  | R0 => Ob~0
  end.

Definition rules (rl: rule_name_t) : rule R empty_Sigma :=
  match rl with end.

Definition package :=
  {| ip_koika := {| koika_reg_types := R;
                   koika_reg_init := r;
                   koika_ext_fn_types := empty_Sigma;
                   koika_rules := rules;
                   koika_scheduler := empty_scheduler;
                   koika_module_name := "empty" |};
     ip_sim := {| sp_ext_fn_names := empty_fn_names;
                 sp_extfuns := None |};
     ip_verilog := {| vp_ext_fn_names := empty_fn_names;
                     vp_external_rules := [] |} |}.

Definition prog := Interop.Backends.register package.
Extraction "errors.ml" prog.
