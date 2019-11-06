Require Import Koika.Frontend.

Module Collatz.
  Inductive reg_t := r0.
  Inductive rule_name_t := divide | multiply.

  Definition logsz := 4.
  Notation sz := (pow2 logsz).

  Definition R r :=
    match r with
    | r0 => bits_t sz
    end.

  Definition r idx : R idx :=
    match idx with
    | r0 => Bits.of_nat sz 19
    end.

  Definition times_three : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun (v: bits_t 16) : bits_t 16 =>
         (v << Ob~1) + v }}.

  Definition _divide : uaction reg_t empty_ext_fn_t :=
    {{ let v := read0(r0) in
       let odd := v[Ob~0~0~0~0] in
       if !odd then
         write0(r0,v >> Ob~1)
       else
         fail }}.

  Definition _multiply : uaction reg_t empty_ext_fn_t :=
    {{ let v := read1(r0) in
       let odd := v[Ob~0~0~0~0] in
       if odd then
         write1(r0, times_three(v) + Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1)
       else
         fail }}.

  Definition collatz : scheduler :=
    tc_scheduler (divide |> multiply |> done).

  Definition cr := ContextEnv.(create) r.

  (* Typechecking  *)
  Definition rules :=
    tc_rules R empty_Sigma
             (fun r => match r with
                    | divide => _divide
                    | multiply => _multiply
                    end).

  Definition result :=
    tc_compute (interp_scheduler cr empty_sigma rules collatz).

  Definition divide_result :=
    tc_compute (interp_action cr empty_sigma CtxEmpty log_empty log_empty
                              (rules divide)).

  Definition multiply_result :=
    tc_compute (interp_action cr empty_sigma CtxEmpty log_empty log_empty
                              (rules multiply)).

  Definition circuits :=
    compile_scheduler rules collatz.

  Definition circuits_result :=
    tc_compute (interp_circuits (ContextEnv.(create) r) empty_sigma circuits).

  Definition koika_package :=
    {| koika_reg_types := R;
       koika_reg_init := r;
       koika_reg_finite := _;

       koika_ext_fn_types := empty_Sigma;
       koika_reg_names := show;

       koika_rules := rules;
       koika_rule_names := show;

       koika_scheduler := collatz;
       koika_module_name := "collatz" |}.

  Definition package :=
    {| ip_koika := koika_package;
       ip_sim := {| sp_var_names x := x;
                   sp_ext_fn_names := empty_fn_names;
                   sp_extfuns := None |};
       ip_verilog := {| vp_external_rules := List.nil;
                       vp_ext_fn_names := empty_fn_names |} |}.
End Collatz.

Definition prog := Interop.Backends.register Collatz.package.
Extraction "collatz.ml" prog.
