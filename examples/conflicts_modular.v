(*! Understanding conflicts and forwarding, with modules !*)
Require Import Koika.Frontend.

Module Import Queue32.
  Inductive reg_t := empty | data.
  Definition R reg :=
    match reg with
    | empty => bits_t 1
    | data => bits_t 32
    end.

  Definition dequeue0: UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun dequeue0 () : bits_t 32 =>
         guard(!read0(empty)); write0(empty, Ob~1); read0(data) }}.

  Definition enqueue0: UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun enqueue0 (val: bits_t 32) : unit_t =>
         guard(read0(empty)); write0(empty, Ob~0); write0(data, val) }}.

  Definition dequeue1: UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun dequeue1 () : bits_t 32 =>
         guard(!read1(empty)); write1(empty, Ob~1); read1(data) }}.
End Queue32.

Inductive reg_t :=
| in0: Queue32.reg_t -> reg_t
| in1: Queue32.reg_t -> reg_t
| fifo: Queue32.reg_t -> reg_t
| out: Queue32.reg_t -> reg_t.

Inductive rule_name_t := deq0 | deq1 | process.

Definition R (reg: reg_t) : type :=
  match reg with
  | in0 st => Queue32.R st
  | in1 st => Queue32.R st
  | fifo st => Queue32.R st
  | out st => Queue32.R st
  end.

Definition urules (rl: rule_name_t) : uaction reg_t empty_ext_fn_t :=
  match rl with
  | deq0 =>
    {{ fifo.(enqueue0)(in0.(dequeue0)()) }}
  | deq1 =>
    {{ fifo.(enqueue0)(in1.(dequeue0)()) }}
  | process =>
    {{ out.(enqueue0)(|32`d412| + fifo.(dequeue1)()) }}
  end.

Definition rules : rule_name_t -> rule R empty_Sigma :=
  tc_rules R empty_Sigma urules.

Definition pipeline : scheduler :=
  deq0 |> deq1 |> process |> done.

Definition external (r: rule_name_t) := false.

Definition r (reg: reg_t) : R reg :=
  match reg with
  | in0 empty => Ob~0
  | in0 data => Bits.of_nat _ 42
  | in1 empty => Ob~0
  | in1 data => Bits.of_nat _ 73
  | fifo empty => Ob~1
  | fifo data => Bits.zero
  | out empty => Ob~1
  | out data => Bits.zero
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
                   koika_module_name := "conflicts_modular" |};

     ip_sim := {| sp_ext_fn_names := empty_ext_fn_names;
                 sp_extfuns := None |};

     ip_verilog := {| vp_ext_fn_names := empty_ext_fn_names |} |}.

Definition prog := Interop.Backends.register package.
Extraction "conflicts_modular.ml" prog.
