(*! Calling external functions !*)
Require Import Koika.Frontend.

Inductive reg_t := pc | next_instr_int | next_instr_ext.
Inductive ext_fn_t := nth_instr_external.
Inductive rule_name_t := fetch_internal | fetch_external | incr_pc.

Definition instructions : list (uaction reg_t ext_fn_t) :=
  Eval vm_compute in
    [{{ Ob~1~1~0~1~1~0~0~0~0~0~1~0~1~1~0~0~0~0~0~0~0~1~1~1~1~1~0~0~1~1~0~1 }};
     {{ Ob~0~1~1~0~1~0~1~1~1~0~1~0~1~0~1~0~1~0~0~1~0~1~0~0~0~1~0~1~0~1~0~1 }};
     {{ Ob~1~0~0~0~0~0~1~0~1~1~1~0~0~0~1~0~1~1~1~0~0~1~1~0~0~1~1~0~0~0~1~0 }};
     {{ Ob~0~1~1~1~1~0~1~0~0~0~0~0~0~0~1~0~0~1~0~0~0~0~1~0~0~0~0~0~0~1~0~0 }};
     {{ Ob~1~1~1~0~1~0~0~0~0~1~1~1~1~0~1~0~0~0~0~1~0~1~1~0~0~0~0~1~0~0~1~1 }};
     {{ Ob~1~0~0~0~0~0~0~1~0~0~1~1~0~0~1~1~0~0~1~0~1~0~0~0~0~1~1~1~0~1~1~0 }};
     {{ Ob~0~1~0~0~1~0~0~0~0~0~1~0~0~1~1~0~1~0~0~0~0~1~1~0~0~1~1~1~0~0~1~1 }};
     {{ Ob~1~1~0~0~0~0~0~1~0~1~1~1~1~1~0~0~0~1~1~0~0~0~1~0~0~1~1~1~1~0~0~1 }}].

Definition R r :=
  match r with
  | pc => bits_t 5
  | next_instr_int => bits_t 32
  | next_instr_ext => bits_t 32
  end.

Definition r idx : R idx :=
  match idx with
  | pc => Bits.zero
  | next_instr_int => Bits.zero
  | next_instr_ext => Bits.zero
  end.

Definition Sigma (fn: ext_fn_t) : ExternalSignature :=
  match fn with
  | fetch_instr => {$ bits_t 3 ~> bits_t 32 $}
  end.

Definition nth_instr_intfun : UInternalFunction reg_t ext_fn_t :=
  {{ fun nth_instr_intfun (addr: bits_t 3) : bits_t 32 =>
       `UCompleteSwitch NestedSwitch 3
        "addr" (List_nth instructions)` }}.

Definition _fetch_internal : uaction reg_t ext_fn_t :=
  {{ let addr := (read0(pc) >> |5`d2|)[Ob~0~0~0 :+ 3] in
     write0(next_instr_int, nth_instr_intfun(addr)) }}.

Definition _fetch_external : uaction reg_t ext_fn_t :=
  {{ let addr := (read0(pc) >> |5`d2|)[Ob~0~0~0 :+ 3] in
     write0(next_instr_ext, extcall nth_instr_external(addr)) }}.

Definition plus4 : UInternalFunction reg_t ext_fn_t :=
  {{ fun plus4 (v: bits_t 5) : bits_t 5 =>
       v + |5`d4| }}.

Definition _incr_pc : uaction reg_t ext_fn_t :=
  {{ write0(pc, plus4(read0(pc))) }}.

Definition rules :=
  tc_rules R Sigma
           (fun r => match r with
                  | fetch_internal => _fetch_internal
                  | fetch_external => _fetch_external
                  | incr_pc => _incr_pc
                  end).

Definition sched : scheduler :=
  fetch_internal |> fetch_external |> incr_pc |> done.

Definition ext_fn_names (fn: ext_fn_t) :=
  match fn with
  | nth_instr_external => "fetch_instr"
  end.

Definition package :=
  {| ip_koika := {| koika_reg_types := R;
                   koika_reg_init := r;
                   koika_ext_fn_types := Sigma;
                   koika_rules := rules;
                   koika_rule_external _ := false;
                   koika_scheduler := sched;
                   koika_module_name := "function_call" |};

     ip_sim :=
       {| sp_ext_fn_names := ext_fn_names;
          sp_extfuns := Some "#include ""extfuns.hpp""" |};

     ip_verilog := {| vp_ext_fn_names := ext_fn_names |} |}.

Unset Extraction Optimize.
Definition prog := Interop.Backends.register package.
Extraction "function_call.ml" prog.
