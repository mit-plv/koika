Require Import Koika.Frontend.

Inductive reg_t := pc | next_instr.
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

Notation instr_sz := 32.
Notation pc_sz := (log2 (List.length instructions)).

Definition R r :=
  match r with
  | pc => bits_t pc_sz
  | next_instr => bits_t 32
  end.

Definition r idx : R idx :=
  match idx with
  | pc => Bits.zero
  | next_instr => Bits.zero
  end.

Definition Sigma (fn: ext_fn_t) : ExternalSignature :=
  match fn with
  | fetch_instr => {$ bits_t 3 ~> bits_t 32 $}
  end.

Definition nth_instr_intfun : UInternalFunction reg_t ext_fn_t :=
  {{ fun (pc: bits_t pc_sz) : bits_t instr_sz =>
       `UCompleteSwitch NestedSwitch pc_sz "pc" (List_nth instructions)` }}.

Definition _fetch_internal : uaction reg_t ext_fn_t :=
  {{ let pc := read0(pc) in
     write0(next_instr, nth_instr_intfun(pc)) }}.

Definition _fetch_external : uaction reg_t ext_fn_t :=
  {{ let pc := read0(pc) in
     write1(next_instr, extcall nth_instr_external(pc)) }}.

Definition plus4 : UInternalFunction reg_t ext_fn_t :=
  {{ fun (v: bits_t pc_sz) : bits_t pc_sz =>
       v + |pc_sz`d4| }}.

Definition _incr_pc : uaction reg_t ext_fn_t :=
  {{ write0(pc, plus4(read0(pc))) }}.

Definition rules :=
  tc_rules R Sigma
           (fun r => match r with
                  | fetch_internal => _fetch_internal
                  | fetch_external => _fetch_external
                  | incr_pc => _incr_pc
                  end).

Definition sched :=
  tc_scheduler (fetch_internal |> fetch_external |> incr_pc |> done).

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
          sp_extfuns := Some "#include ""../function_call.extfuns.hpp""" |};

     ip_verilog := {| vp_ext_fn_names := ext_fn_names |} |}.

Unset Extraction Optimize.
Definition prog := Interop.Backends.register package.
Extraction "function_call.ml" prog.
