(*! Calling methods of internal modules !*)
Require Import Koika.Frontend.
Require Import Koika.Std.


Definition ext_fn_t := empty_ext_fn_t.

(* Definition submodule *)
Module Delay.
  Inductive reg_t := buffer.

  (* Declaration of a Koika function in a module, called a method *)
  Definition swap tau: UInternalFunction reg_t ext_fn_t  :=
    {{
        fun swap (arg1 : tau) : tau =>
          write0(buffer, arg1);
          read0(buffer)
    }}.

  Instance FiniteType_reg_t : FiniteType reg_t := _.
End Delay.

(* Declare state, with submodule instances *)
Inductive reg_t := rA | rDelay1 (d: Delay.reg_t) | rDelay2 (d: Delay.reg_t).
Inductive rule_name_t := rl.

(* Types of state *)
Definition R r :=
  match r with
  | rA => bits_t 16
  | rDelay1 buffer => bits_t 8
  | rDelay2 buffer => bits_t 16
  end.

(* Init value of state *)
Definition r reg : R reg :=
  match reg with
  | rA => Bits.of_N _ 12
  | rDelay1 buffer => Bits.zero
  | rDelay2 buffer => Bits.zero
  end.

(* Declaration of a family of Koika function indexed by a coq integer *)
Definition nor (sz: nat) : UInternalFunction reg_t ext_fn_t :=
  {{
      fun nor (arg1 : bits_t sz) (arg2 : bits_t sz) : bits_t sz =>
        !(arg1 || arg2)
  }}.

Definition display :=
  (Display.Printer (ext_fn_t := empty_ext_fn_t) (reg_t := reg_t) (pos_t := pos_t)).

Definition swap16 := Delay.swap (bits_t 16).

Definition _rl : uaction reg_t empty_ext_fn_t :=
  {{
      let a := read0(rA) in
       (* Methods are called as reg.(method)(args...) *)
      let old_a := rDelay2.(swap16)(a) in
      (* Parametric functions can be called with {fn params...}(args...) *)
      write0(rA, {nor 16}(read0(rA), old_a));
      {display [Display.Str "rA: "; Display.Value (bits_t 16)]}(a)
  }}.

Definition rules :=
  tc_rules R empty_Sigma
           (fun rl => match rl with
                   | rl => _rl
                   end).

Definition sched : scheduler :=
  rl |> done.

Instance FiniteType_reg_t : FiniteType reg_t := _.

Definition external (r: rule_name_t) := false.

Definition circuits :=
  compile_scheduler rules external sched.

Definition cr := ContextEnv.(create) r.

Definition interp_result :=
  tc_compute (commit_update cr (interp_scheduler cr empty_sigma rules sched)).

Definition circuits_result :=
  tc_compute (interp_circuits empty_sigma circuits (lower_r cr)).

Definition package :=
  {| ip_koika := {| koika_reg_types := R;
                   koika_reg_init := r;
                   koika_ext_fn_types := empty_Sigma;
                   koika_rules := rules;
                   koika_rule_external := external;
                   koika_scheduler := sched;
                   koika_module_name := "intfn" |};

     ip_sim := {| sp_ext_fn_specs := empty_ext_fn_props;
                 sp_prelude := None |};

     ip_verilog := {| vp_ext_fn_specs := empty_ext_fn_props |} |}.

Definition prog := Interop.Backends.register package.
Extraction "method_call.ml" prog.
