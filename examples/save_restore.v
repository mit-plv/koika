(*! Save and restore simulation state !*)
Require Import Koika.Frontend.

Module SaveRestore.
  Inductive reg_t := counter.
  Inductive rule_name_t := increment_counter.

  Definition R r :=
    match r with
    | counter => bits_t 32
    end.

  Definition r idx : R idx :=
    match idx with
    | counter => Bits.zero
    end.

  Definition _increment_counter : uaction reg_t empty_ext_fn_t :=
    {{ write0(counter, read0(counter) + |32`d1|) }}.

  Definition save_restore : scheduler :=
    increment_counter |> done.

  Definition rules :=
    tc_rules R empty_Sigma
             (fun r => match r with
                    | increment_counter => _increment_counter
                    end).

  Definition external (_: rule_name_t) := false.

  Definition package :=
    {| ip_koika := {| koika_reg_types := R;
                     koika_reg_init := r;
                     koika_ext_fn_types := empty_Sigma;
                     koika_rules := rules;
                     koika_rule_external := external;
                     koika_scheduler := save_restore;
                     koika_module_name := "save_restore" |};

       ip_sim := {| sp_ext_fn_specs := empty_ext_fn_props;
                   sp_prelude := None |};

       ip_verilog := {| vp_ext_fn_specs := empty_ext_fn_props |} |}.
End SaveRestore.

Definition prog := Interop.Backends.register SaveRestore.package.
