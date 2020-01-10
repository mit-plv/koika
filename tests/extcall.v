(*! External functions !*)
Require Import Koika.Frontend.

Inductive reg_t := reg0.
Inductive ext_fn_t := f0.
Inductive rule_name_t := rl0.

Definition R reg : type :=
  match reg with
  | reg0 => bits_t 3
  end.

Definition Sigma fn : ExternalSignature :=
  match fn with
  | f0 => {$ bits_t 3 ~> bits_t 3 $}
  end.

Definition r reg : R reg :=
  match reg with
  | reg0 => Ob~1~0~1
  end.

Definition sigma fn : Sig_denote (Sigma fn) :=
  match fn with
  | f0 => fun (bs: bits 3) => Bits.neg bs
  end.

Definition urules rl : uaction reg_t ext_fn_t :=
  match rl with
  | rl0 => {{ write0(reg0, extcall f0(read0(reg0))) }}
  end.

Definition rules :=
  tc_rules R Sigma urules.

Definition sched : scheduler :=
  rl0 |> done.

Definition sched_result :=
  tc_compute (interp_scheduler (ContextEnv.(create) r) sigma rules sched).

Definition external (r: rule_name_t) := false.

Definition sched_circuits :=
  compile_scheduler rules external sched.

Definition sched_circuits_result :=
  tc_compute (interp_circuits (ContextEnv.(create) r) sigma sched_circuits).

Definition cpp_ext_fn_names fn := match fn with f0 => "cpp_f0" end.
Definition verilog_ext_fn_names fn := match fn with f0 => "verilog_f0" end.

Definition package :=
  {| ip_koika := {| koika_reg_types := R;
                   koika_reg_init := r;
                   koika_ext_fn_types := Sigma;
                   koika_rules := rules;
                   koika_rule_external := external;
                   koika_scheduler := sched;
                   koika_module_name := "extcall" |};

     ip_sim := {| sp_ext_fn_names := cpp_ext_fn_names;
                 sp_extfuns := Some "class extfuns {
public:
  bits<3> cpp_f0(const bits<3> arg) {
    return ~arg;
  }
};" |};

     ip_verilog := {| vp_ext_fn_names := verilog_ext_fn_names |} |}.

Definition prog := Interop.Backends.register package.
Extraction "extcall.ml" prog.
