(*! Double-write detection and prevention !*)
Require Import Koika.Frontend.

Inductive reg_t := reg0.
Inductive rule_name_t := wr0 | skip | wr0_fail.

Definition R reg : type :=
  match reg with
  | reg0 => bits_t 1
  end.

Definition r reg : R reg :=
  match reg with
  | reg0 => Ob~0
  end.

Definition urules rl : uaction reg_t empty_ext_fn_t :=
  match rl with
  | wr0 => {{ write0(reg0, |1`d0|) }}
  | skip => {{ if |1`d0| then write0(reg0, |1`d0|) else pass }}
  | wr0_fail => {{ write0(reg0, |1`d1|) }}
  end.

Definition rules :=
  tc_rules R empty_Sigma urules.

Definition sched : scheduler :=
  wr0 |> skip |> wr0_fail |> done.

Definition sched_result :=
  tc_compute (interp_scheduler (ContextEnv.(create) r) empty_sigma rules sched).

Definition external (r: rule_name_t) := false.

Definition sched_circuits :=
  compile_scheduler rules external sched.

Definition sched_circuits_result :=
  tc_compute (interp_circuits empty_sigma sched_circuits (lower_r (ContextEnv.(create) r))).

Definition package :=
  {| ip_koika := {| koika_reg_types := R;
                   koika_reg_init := r;
                   koika_ext_fn_types := empty_Sigma;
                   koika_rules := rules;
                   koika_rule_external := external;
                   koika_scheduler := sched;
                   koika_module_name := "double_write" |};

     ip_sim := {| sp_ext_fn_specs := empty_ext_fn_props;
                 sp_prelude := None |};

     ip_verilog := {| vp_ext_fn_specs := empty_ext_fn_props |} |}.

Definition prog := Interop.Backends.register package.
Extraction "double_write.ml" prog.
