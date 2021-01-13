(*! Detect and reject programs that call read1 after write1 in simulation !*)
Require Import Koika.Frontend.

Inductive reg_t :=
| yes_plain | yes_if | yes_function | yes_spurious
| no_plain | no_function.
Inductive rule_name_t := weird.

Definition R (reg: reg_t) := bits_t 1.
Definition r reg : R reg := Ob~0.

Definition fn : UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun fn (b1: bits_t 1) (b2: bits_t 1) : bits_t 1 => b1 + b2 }}.

Definition pr : UInternalFunction reg_t empty_ext_fn_t :=
  SyntaxMacros.Display.Printer [SyntaxMacros.Display.Value (bits_t 1)].

Definition urules rl : uaction reg_t empty_ext_fn_t :=
  match rl with
  | weird => {{
      write1(yes_plain, Ob~0);
      pr(read1(yes_plain));

      pr(fn((write1(yes_function, Ob~0); Ob~1),
            read1(yes_function)));

      if Ob~1 then write1(yes_if, Ob~0) else pass;
      if Ob~1 then pr(read1(yes_if)) else pass;

      (* The write1 → read1 check is a static approximation *)
      if Ob~0 then write1(yes_spurious, Ob~0) else pass;
      if Ob~1 then pr(read1(yes_spurious)) else pass;

      pr(read1(no_plain));
      write1(no_plain, Ob~0);

      pr(fn(read1(no_function),
            (write1(no_function, Ob~0); Ob~1)))
    }}
  end.

Definition rules :=
  tc_rules R empty_Sigma urules.

Definition sched : scheduler :=
  weird |> done.

Definition sched_result := (* All yes_… registers have a read1 followed by a write1 *)
  tc_compute (interp_scheduler (ContextEnv.(create) r) empty_sigma rules sched).

Definition external (r: rule_name_t) := false.

Definition package :=
  {| ip_koika := {| koika_reg_types := R;
                   koika_reg_init := r;
                   koika_ext_fn_types := empty_Sigma;
                   koika_rules := rules;
                   koika_rule_external := external;
                   koika_scheduler := sched;
                   koika_module_name := "read1_write1_check" |};

     ip_sim := {| sp_ext_fn_specs := empty_ext_fn_props;
                 sp_prelude := None |};

     ip_verilog := {| vp_ext_fn_specs := empty_ext_fn_props |} |}.

Definition prog := Interop.Backends.register package.
Extraction "read1_write1_check.ml" prog.
