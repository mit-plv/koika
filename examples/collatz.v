(*! Computing terms of the Collatz sequence (Coq version) !*)
Require Import Koika.Frontend.

Module Collatz.
  (*! We have one register ``r0``: !*)
  Inductive reg_t := r0.
  (*! …and two rules ``divide`` and ``multiply``: !*)
  Inductive rule_name_t := divide | multiply.

  Definition logsz := 4.
  Notation sz := (pow2 logsz).

  (*! ``r0`` is a register storing 2^4 = 16 bits: !*)
  Definition R r :=
    match r with
    | r0 => bits_t sz
    end.

  (*! ``r0`` is initialized to 18: !*)
  Definition r idx : R idx :=
    match idx with
    | r0 => Bits.of_nat sz 18
    end.

  Definition times_three : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun times_three (bs: bits_t 16) : bits_t 16 =>
         (bs << Ob~1) + bs }}.

  (*! Our first rule, ``divide``, reads from r0 and halves the result if it's even: !*)
  Definition _divide : uaction reg_t empty_ext_fn_t :=
    {{ let v := read0(r0) in
       let odd := v[Ob~0~0~0~0] in
       if !odd then
         write0(r0,v >> Ob~1)
       else
         fail }}.

  (*! Our second rule, ``multiply``, reads the output of ``divide`` and
      multiplies it by three and ads one if it is odd: !*)
  Definition _multiply : uaction reg_t empty_ext_fn_t :=
    {{ let v := read1(r0) in
       let odd := v[Ob~0~0~0~0] in
       if odd then
         write1(r0, times_three(v) + Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1)
       else
         fail }}.

  (*! The design's schedule defines the order in which rules should (appear to) run !*)
  Definition collatz : scheduler :=
    divide |> multiply |> done.

  Definition cr := ContextEnv.(create) r.

  (*! Rules are written in an untyped language, so we need to typecheck them: !*)
  Definition rules :=
    tc_rules R empty_Sigma
             (fun r => match r with
                    | divide => _divide
                    | multiply => _multiply
                    end).

  (*! And now we can compute results: uncomment the ``Print`` commands below to show results. !*)

  Definition divide_result :=
    tc_compute (interp_action cr empty_sigma CtxEmpty log_empty log_empty
                              (rules divide)).

  (*! The output of ``divide`` when ``r0 = 18``: a write to ``r0`` with value ``0b1001 = 9``: !*)
  (* Print divide_result. *)

  Definition multiply_result :=
    tc_compute
      (let '(log, _, _) := must divide_result in
       interp_action cr empty_sigma CtxEmpty log_empty log (rules multiply)).

  (*! The output of ``multiply`` when ``r0 = 9``: a write to ``r0`` with value ``0b11100 = 28``: !*)
  (* Print multiply_result. *)

  Definition cycle_log :=
    tc_compute (interp_scheduler cr empty_sigma rules collatz).

  (*! The complete log over the first cycle: two writes to ``r0`` !*)
  (* Print cycle_log. *)

  Definition result :=
    tc_compute (commit_update cr cycle_log).

  (*! The values of the registers after the first cycle completes: ``r0 = 28`` !*)
  (* Print result. *)

  Definition external (r: rule_name_t) := false.

  Definition circuits :=
    compile_scheduler rules external collatz.

  Definition circuits_result :=
    tc_compute (interp_circuits empty_sigma circuits (lower_r (ContextEnv.(create) r))).

  (*! The same values computed by running compiled circuits: ``r0 = 28`` !*)
  (* Print circuits_result. *)

  Example test: circuits_result = Environments.map _ (fun _ => bits_of_value) result :=
    eq_refl.

  (*! This package configures compilation to C++ with Cuttlesim and Verilog with Kôika's verified compiler: !*)
  Definition package :=
    {| ip_koika := {| koika_reg_types := R;
                     koika_reg_init := r;
                     koika_ext_fn_types := empty_Sigma;
                     koika_rules := rules;
                     koika_rule_external := external;
                     koika_scheduler := collatz;
                     koika_module_name := "collatz" |};

       ip_sim := {| sp_ext_fn_specs := empty_ext_fn_props;
                   sp_prelude := None |};

       ip_verilog := {| vp_ext_fn_specs := empty_ext_fn_props |} |}.
End Collatz.

(*! This is the entry point used by the compiler: !*)
Definition prog := Interop.Backends.register Collatz.package.
