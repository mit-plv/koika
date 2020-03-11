(*! Definition of a pipelined schedule !*)
Require Import Koika.Frontend.
Require Import RV.RVCore.

Definition rv_schedule : scheduler :=
  Writeback |> Execute |> StepMultiplier |> Decode |> WaitImem |> Fetch |> Imem |> Dmem |> UART_write |> Tick |> done.

Module Package (C: Core).
  Import C.
  Existing Instance Show_reg_t.
  Existing Instance Show_ext_fn_t.
  Existing Instance FiniteType_reg_t.

  Definition circuits :=
    compile_scheduler rv_rules rv_external rv_schedule.

  Definition koika_package :=
    {| koika_reg_types := R;
       koika_reg_init := r;
       koika_ext_fn_types := Sigma;
       koika_rules := rv_rules;
       koika_rule_external := rv_external;
       koika_scheduler := rv_schedule;
       koika_module_name := "rv32" |}.

  Definition package :=
    {| ip_koika := koika_package;
       ip_sim := {| sp_ext_fn_names fn := show fn;
                   sp_extfuns := None |};
       ip_verilog := {| vp_ext_fn_specs := rv_ext_fn_specs |} |}.
End Package.
