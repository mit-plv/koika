(*! Cross-cycle optimization in Cuttlesim models !*)
(* The way Cuttlesim is designed enables GCC to completely reduce this calculation *)
Require Import Koika.Frontend.

Inductive reg_t := a.
Inductive rule_name_t := rl.

Definition R (reg: reg_t) : type :=
  match reg with
  | a => bits_t 5
  end.

Definition urules rl : uaction reg_t empty_ext_fn_t :=
  match rl with
  | rl => {{ write0(a, if read0(a)[Ob~0~0~0] then Ob~0~1~0~1~0 else Ob~1~1~0~1~0) }}
  end.

Definition rules :=
  tc_rules R empty_Sigma urules.

Definition sched : scheduler :=
  rl |> done.

Definition external (r: rule_name_t) := false.

Definition r (reg: reg_t) : R reg :=
  match reg with
  | a => Bits.zero
  end.

Definition cr := ContextEnv.(create) r.

Definition interp_result :=
  tc_compute (commit_update cr (interp_scheduler cr empty_sigma rules sched)).

Definition circuits :=
  compile_scheduler rules external sched.

Definition circuits_result :=
  tc_compute (interp_circuits cr empty_sigma circuits).

Definition package :=
  {| ip_koika := {| koika_reg_types := R;
                   koika_reg_init reg := r reg;
                   koika_ext_fn_types := empty_Sigma;
                   koika_rules := rules;
                   koika_rule_external := external;
                   koika_scheduler := sched;
                   koika_module_name := "cross_cycle" |};

     ip_sim := {| sp_ext_fn_specs := empty_ext_fn_props;
                 sp_prelude := None |};

     ip_verilog := {| vp_ext_fn_specs := empty_ext_fn_props |} |}.

Definition prog := Interop.Backends.register package.
Extraction "cross_cycle.ml" prog.
