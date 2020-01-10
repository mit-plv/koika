(*! Understanding conflicts and forwarding !*)
Require Import Koika.Frontend.

Inductive reg_t :=
| in0_empty | in0_data
| in1_empty | in1_data
| fifo_empty | fifo_data
| out_empty | out_data.

Inductive rule_name_t := deq0 | deq1 | process.

Definition R (reg: reg_t) : type :=
  match reg with
  | in0_empty | in1_empty | fifo_empty | out_empty => bits_t 1
  | in0_data | in1_data | fifo_data | out_data => bits_t 32
  end.

Definition urules (rl: rule_name_t) : uaction reg_t empty_ext_fn_t :=
  match rl with
  | deq0 =>
    {{ guard(!read0(in0_empty) && read0(fifo_empty));
       write0(fifo_data, read0(in0_data));
       write0(fifo_empty, Ob~0);
       write0(in0_empty, Ob~1) }}
  | deq1 =>
    {{ guard(!read0(in1_empty) && read0(fifo_empty));
       write0(fifo_data, read0(in1_data));
       write0(fifo_empty, Ob~0);
       write0(in1_empty, Ob~1) }}
  | process =>
    {{ guard(!read1(fifo_empty) && read0(out_empty));
       write0(out_data, read1(fifo_data) + |32`d412|);
       write1(fifo_empty, Ob~1);
       write0(out_empty, Ob~0) }}
  end.

Definition rules : rule_name_t -> rule R empty_Sigma :=
  tc_rules R empty_Sigma urules.

Definition pipeline : scheduler :=
  deq0 |> deq1 |> process |> done.

Definition external (r: rule_name_t) := false.

Definition r (reg: reg_t) : R reg :=
  match reg with
  | in0_empty => Ob~0
  | in0_data => Bits.of_nat _ 42
  | in1_empty => Ob~0
  | in1_data => Bits.of_nat _ 73
  | fifo_empty => Ob~1
  | fifo_data => Bits.zero
  | out_empty => Ob~1
  | out_data => Bits.zero
  end.

Definition cr := ContextEnv.(create) r.

Definition interp_result :=
  tc_compute (commit_update cr (interp_scheduler cr empty_sigma rules pipeline)).

Definition circuits :=
  compile_scheduler rules external pipeline.

Definition circuits_result :=
  tc_compute (interp_circuits cr empty_sigma circuits).

Definition package :=
  {| ip_koika := {| koika_reg_types := R;
                   koika_reg_init reg := r reg;
                   koika_ext_fn_types := empty_Sigma;
                   koika_rules := rules;
                   koika_rule_external := external;
                   koika_scheduler := pipeline;
                   koika_module_name := "conflicts" |};

     ip_sim := {| sp_ext_fn_names := empty_ext_fn_names;
                 sp_extfuns := None |};

     ip_verilog := {| vp_ext_fn_names := empty_ext_fn_names |} |}.

Definition prog := Interop.Backends.register package.
Extraction "conflicts.ml" prog.
