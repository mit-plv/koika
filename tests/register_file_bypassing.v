(*! Ensure that area is reasonable when bypasses don't need extra tracking !*)
Require Import Koika.Frontend.
Require Import Koika.Std.

Definition data_sz := 13.
Definition data_tau := bits_t data_sz.
Definition idx_sz := 2.

Module Rf4_sig <: RfPow2_sig.
  Definition idx_sz := idx_sz.
  Definition T := data_tau.
  Definition init := Bits.zeroes data_sz.
  Definition read_style := SequentialSwitch data_tau "tmp".
  Definition write_style := @SequentialSwitchTt var_t.
End Rf4_sig.

Module Rf4 := RfPow2 Rf4_sig.

Inductive reg_t := rd_idx | rd_output | wb_should_writeback | wb_idx | wb_input | rf (idx: Rf4.reg_t).
Inductive rule_name_t := read_nth | writeback.

Definition R reg : type :=
  match reg with
  | rd_idx => bits_t idx_sz
  | rd_output => data_tau
  | wb_should_writeback => bits_t 1
  | wb_idx => bits_t idx_sz
  | wb_input => data_tau
  | rf idx => Rf4.R idx
  end.

Definition r reg : R reg :=
  match reg with
  | rd_idx => Bits.of_nat idx_sz 3
  | rd_output => Bits.zero
  | wb_idx => Bits.of_nat idx_sz 1
  | wb_should_writeback => Bits.one
  | wb_input => Bits.of_nat data_sz 42
  | rf idx => Rf4.r idx
  end.

Definition _read_nth : uaction reg_t empty_ext_fn_t :=
  {{ let idx := read0(rd_idx) in
     let v := rf.(Rf4.read_1)(idx) in
     write0(rd_output, v) }}.

Definition _writeback : uaction reg_t empty_ext_fn_t :=
  {{ let idx := read0(wb_idx) in
     let v := read0(wb_input) in
     if read0(wb_should_writeback) then
       rf.(Rf4.write_0)(idx, v)
     else pass }}.

Definition urules rl : uaction reg_t empty_ext_fn_t :=
  match rl with
  | read_nth => _read_nth
  | writeback => _writeback
  end.

Definition rules :=
  tc_rules R empty_Sigma urules.

Definition sched : scheduler :=
  writeback |> read_nth |> done.

Instance FiniteType_Rf4_reg_t : FiniteType Rf4.reg_t := _.

Definition sched_result :=
  tc_compute (interp_scheduler (ContextEnv.(create) r) empty_sigma rules sched).

Definition external (r: rule_name_t) := false.

Definition sched_circuits :=
  compile_scheduler rules external sched.

Definition sched_circuits_result :=
  tc_compute (interp_circuits (ContextEnv.(create) r) empty_sigma sched_circuits).

Definition package :=
  {| ip_koika := {| koika_reg_types := R;
                   koika_reg_init := r;
                   koika_ext_fn_types := empty_Sigma;
                   koika_rules := rules;
                   koika_rule_external := external;
                   koika_scheduler := sched;
                   koika_module_name := "register_file_bypassing" |};

     ip_sim := {| sp_ext_fn_specs := empty_ext_fn_props;
                 sp_prelude := None |};

     ip_verilog := {| vp_ext_fn_specs := empty_ext_fn_props |} |}.

Definition prog := Interop.Backends.register package.
Extraction "register_file_bypassing.ml" prog.
