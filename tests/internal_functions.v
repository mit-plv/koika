(*! Intfun tests !*)
Require Import Koika.Frontend.

Inductive reg_t := reg0.
Inductive rule_name_t := rl0.
Definition R reg : type := match reg with reg0 => bits_t 1 end.
Definition r reg : R reg := match reg with reg0 => Ob~0 end.

Definition snd : UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun snd (x: bits_t 1) (y: bits_t 1) : bits_t 1 => (y ++ x)[Ob~0] }}.

Definition urules rl : uaction reg_t empty_ext_fn_t :=
  match rl with
  | rl0 => {{ let x := read0(reg0) in
             let y := Ob~0 in
             write0(reg0, snd(y, x)) }}
  end.

(* When typechecked and lowered, this program produces this:

   let x#0 := read0(reg0) in
   let y#0 := Ob~0 in
   let y#1 := x#0 in
   let x#1 := y#0 in
   y#1

Note that this isn't equivalent to this:

   let x := read0(reg0) in
   let y := Ob~0 in
   let y := x in
   let x := y in
   y *)

Definition rules :=
  tc_rules R empty_Sigma urules.

Definition lowered :=
  (fun rl => match rl with
          | rl0 => Lowering.lower_action (rules rl0)
          end).

Definition sched : scheduler := rl0 |> done.

Definition sched_result :=
  tc_compute (interp_scheduler (ContextEnv.(create) r) empty_sigma rules sched).

Definition external (r: rule_name_t) := false.

Definition package :=
  {| ip_koika := {| koika_reg_types := R;
                   koika_reg_init := r;
                   koika_ext_fn_types := empty_Sigma;
                   koika_rules := rules;
                   koika_rule_external := external;
                   koika_scheduler := sched;
                   koika_module_name := "internal_functions" |};

     ip_sim := {| sp_ext_fn_specs := empty_ext_fn_props;
                 sp_prelude := None |};

     ip_verilog := {| vp_ext_fn_specs := empty_ext_fn_props |} |}.

Definition prog := Interop.Backends.register package.
Extraction "internal_functions.ml" prog.
