(*! Trivial state machine !*)
Require Import Koika.Frontend.

Definition SZ := 32.
Inductive reg_t := st | internal.
Inductive rule_name_t := rlA | rlB.
Inductive ext_fn_t := extA | extB.

Definition state_t :=
  {| enum_name := "state";
     enum_members := ["A"; "B"];
     enum_bitpatterns := [Ob~0; Ob~1] |}%vect.

Definition R reg : type :=
  match reg with
  | st => enum_t state_t
  | internal => bits_t SZ
  end.

Definition Sigma fn : ExternalSignature :=
  match fn with
  | extA => {$ bits_t SZ ~> bits_t SZ $}
  | extB => {$ bits_t SZ ~> bits_t SZ $}
  end.

Definition r reg : R reg :=
  match reg with
  | st => Ob~0
  | internal => Bits.zero
  end.

Definition urules rl : uaction reg_t ext_fn_t :=
  match rl with
  | rlA => {{ guard(read0(st) == enum state_t{A});
             write0(st, enum state_t{B});
             write0(internal, extcall extA(read0(internal))) }}
  | rlB => {{ guard(read0(st) == enum state_t{B});
             write0(st, enum state_t{A});
             write0(internal, extcall extB(read0(internal))) }}
  end.

Definition rules :=
  tc_rules R Sigma urules.

Definition sched : scheduler :=
  rlA |> rlB |> done.

Definition external (r: rule_name_t) := false.

Instance Show_ext_fn_t : Show ext_fn_t := _.

Definition package :=
  {| ip_koika := {| koika_reg_types := R;
                   koika_reg_init := r;
                   koika_ext_fn_types := Sigma;
                   koika_rules := rules;
                   koika_rule_external := external;
                   koika_scheduler := sched;
                   koika_module_name := "trivial_state_machine" |};

     ip_sim := {| sp_ext_fn_specs fn := {| efs_name := show fn;
                                         efs_method := false |};
                 sp_prelude := None |};

     ip_verilog := {| vp_ext_fn_specs fn := {| efr_name := show fn;
                                             efr_internal := true |} |} |}.

Definition prog := Interop.Backends.register package.
Extraction "trivial_state_machine.ml" prog.
