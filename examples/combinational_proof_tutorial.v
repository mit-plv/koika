(*! Tutorial: Verifying a small combinational circuit !*)
Require Import Koika.Frontend.

(*|
============================================================
 A simple combinational module and its proof of correctness
============================================================

In this file we model a simple combinational block:

  input ---(the module)--> output

Unlike in ``combinational_proof_tutorial.v``, we are not concerned here with properties related to timing, and for maximum simplicity we consider a single-cycle, non-combinational proof design.

We will start by verifying a Kôika function, and then show how to extend the proof to a single-rule design.

All that follows is parameterized on a register size ``sz``, set here to 16 bits.
|*)

Definition sz := 16.

(*|
Model
=====

We start by defining our functional model.  We have a type of "instructions", which select the mode of operation of our module:
|*)

Inductive operation :=
| quadruple (** Quadruple the input **)
| rotate_half. (** Rotate the input left by half of its width **)

(*|
Note that this model does not specify the bit pattern to encode those two instructions.
And we have a model of each of these operations:
|*)

Definition model (op: operation) (input: bits sz) : bits sz :=
  match op with
  | quadruple => Bits.slice 0 sz (Bits.mul (Bits.of_nat sz 4) input)
  | rotate_half => Bits.rotate_l (sz / 2) input
  end.

(*|
We chose a relatively low-level model: an alternative would have been to phrase the model in terms on integers, not bitvectors.  For the purposes of this demo, however, a simple bitvector-based model is enough.

We can check that this model behaves as expected:
|*)

Compute Bits.to_nat (model quadruple (Bits.of_nat sz 7)). (* .unfold *)
Compute model rotate_half Ob~1~1~1~1~0~0~0~0~1~0~1~0~1~0~1~0. (* .unfold *)

(*|
Combinational implementation
============================

We then define the Kôika implementation.
Let's consider a machine working with 8-bits instruction words. The machine should identify which
of the two instructions to perform based on a subset of the 8-bits of being high.
So we start by fixing a bit pattern to recognize for each operation :
|*)

Definition ops :=
  {| enum_name := "operations";
     enum_members :=
       vect_of_list ["quadruple"; "rotate_half"];
     enum_bitpatterns :=
       vect_of_list [Ob~0~0~0~0~0~1~1~0; Ob~0~0~0~1~0~0~0~1] |}.

(*|
… and then we implement the design itself.  While the functional model was written for legibility, the design is written for performance.
For example here we replace the multiply-by-4 operation with bitvector operations (slice and append).

Since we are writing a combinational function, the design is parametric on the set of registers `reg_t`:
|*)

  Definition design reg_t : UInternalFunction reg_t empty_ext_fn_t := {{
    fun design (op: bits_t 8) (input: bits_t sz): bits_t sz =>
      match unpack(enum_t ops, op) with
      | enum ops { quadruple } => input[|4`d0|:+14] ++ Ob~0~0
      | enum ops { rotate_half } => input[|4`d0|:+8] ++ input[|4`d8|:+8]
      return default: |16`d0|
      end
  }}.

(*|
The program above is *untyped*; we want to typecheck it; again, since we do not look at registers, we leave `reg_t` and `R` as parameters:
|*)

  Definition tc_design reg_t R :=
    tc_function R empty_Sigma (design reg_t).

(*|
.. note::

   The result of typechecking a term is a bit gnarly.  For cases like this, where we are going to verify properties of a program and hence spend a lot of time looking at its code, Kôika has an experimental *typed* language, found on the `cpitclaudel_typed_parsing`.

Correctness proof
=================

To prove the correctness of our design, we first need to phrase a correctness property; and for that, we need to relate `operations` in the sense of the model and `ops` in the sense of the design:
|*)

  Definition encode_operation op :=
    match op with
    | quadruple => vect_hd ops.(enum_bitpatterns)
    | rotate_half => vect_hd (vect_tl ops.(enum_bitpatterns))
    end.

  Compute encode_operation quadruple. (* .unfold *)
  Compute encode_operation rotate_half. (* .unfold *)

(*|
This is all that's needed to state a theorem.  We'll use Coq's “section” mechanism to parameterize the theorem about all the stateful parts of Kôika's semantics:
|*)

  Section Correctness.
    Context {reg_t: Type} {reg_t_eq_dec: EqDec reg_t}.
    Context {R: reg_t -> type} {REnv: Env reg_t} (r: REnv.(env_t) R).
    Context (L l: CompactLogs.Log R REnv).

(*|
For readability, let's define an abbreviation of the `interp_action` function.
|*)

    Definition run_design op input :=
      let design_inputs :=
          #{ ("op", bits_t 8) => op;
             ("input", bits_t 16) => input }# in
      CompactSemantics.interp_action
        r empty_sigma design_inputs L l (tc_design reg_t R).

(*|
(This is a good point to run a quick sanity check to make sure that our design passes simple smoke tests:)
|*)

    Definition design_result op input :=
      match run_design op input with
      | Some (_, r, _) => Some r
      | None => None
      end.

    Compute Bits.to_nat (must (design_result Ob~0~0~0~0~0~1~1~0 (Bits.of_nat sz 7))). (* .unfold *)
    Compute must (design_result Ob~0~0~0~1~0~0~0~1 Ob~1~1~1~1~0~0~0~0~1~0~1~0~1~0~1~0) : bits_t _. (* .unfold *)

(*|
All good.  Now for the theorem:
|*)

    Theorem design_correct:
      forall op input, exists ctx',
          run_design (encode_operation op) input =
          Some (l, model op input, ctx').
    Proof.
(*|
There are four components to this equality:

- `Some …` means that the Kôika design did not reach a conflict or a dynamic failure.
- `l` is unchanged in `Some (l, …)`: the model does not perform reads nor writes.
- The design produces the right value, as indicated by the `Some (…, model op input, …)` part of the output.
- `ctx'` records the reads and writes made to local variables; that's an implementation detail, so we don't say anything about it.

We are now ready for the proof, which is structured in two parts — one per operator.
|*)

      destruct op; cbv zeta; intros; eexists. (* .unfold *)

(*|
We can use abstract interpretation to compute the results that the design produces.  Ideally we'd prefer to run `simpl`, but `simpl` in Coq is extremely slow; so we use `cbv` instead, carefully passing it a list of things to not simplify:
|*)

      { unfold run_design; rewrite <- interp_action_cps_correct.
        cbv -[Vect.Bits.slice Bits.slice Bits.mul]. (* .unfold *)

(*|
Hence abstract interpretation shows that the design does not fail (we see `Some` on both sides).  Now we need to show that the two ways of doing this computation (the model's way and the design's way) do match up:
|*)

        repeat f_equal; clear. (* .unfold *)

(*|
This a property of multiplication: multiplying by 4 is the same as shifting left by two places, and the moduli line up properly.  We leave it to the reader — it's not entirely trivial!  THe most efficient way to proceed would probably be to use existing theorems on `N.testbit` along with `Bits.to_N`.
|*)

        admit. }

      { unfold run_design; rewrite <- interp_action_cps_correct.
        cbv -[Vect.Bits.slice Bits.slice Bits.mul vect_app Bits.rotate_l]. (* .unfold *)

        apply f_equal.

(*|
No math involved in this property: it's just a rephrasing of rotation as a slice and an append.  We could prove a general theorem for all bitwidths, but because of the way Kôika's definitions are written this property actually simplifies:
|*)

        cbv; reflexivity.
    Admitted.
  End Correctness.

(*|
Now that we have a verified function, we can incorporate it into a rule and then into a design:
|*)

Inductive reg_t := input_op | input_data | output_data.

Definition R r :=
  match r with
  | input_op    => bits_t 8
  | input_data  => bits_t sz
  | output_data => bits_t sz
  end.

Definition _runDesign : uaction _ _ :=
  {{
     let op := read0(input_op) in
     let input := read0(input_data) in
     write0(output_data, {design reg_t}(op, input))
  }}.

Inductive rule_name_t := runDesign.

Definition rules : rule_name_t -> rule R empty_Sigma :=
  tc_rules R empty_Sigma
           (fun rl => match rl with
                   | runDesign => _runDesign
                   end).

Definition system : scheduler :=
  runDesign |> done.

(*|
Extracting to Verilog and C++
=============================
|*)

Definition r : ContextEnv.(env_t) R :=
  #{ input_op => Ob~0~0~0~0~0~1~1~0;
     input_data => Bits.of_nat 16 7;
     output_data => Bits.of_nat 16 0 }#.

Definition package :=
  {| ip_koika := {| koika_reg_types := R;
                   koika_reg_init reg := r.[reg];
                   koika_ext_fn_types := empty_Sigma;
                   koika_rules := rules;
                   koika_rule_external _ := false;
                   koika_scheduler := system;
                   koika_module_name := "combinational_proof_tutorial" |};

     ip_sim := {| sp_ext_fn_specs := empty_ext_fn_props;
                 sp_prelude := None |};

     ip_verilog := {| vp_ext_fn_specs := empty_ext_fn_props |} |}.

(*|
This last bit registers our program, which allows the build system to locate it:
|*)

Definition prog := Interop.Backends.register package.
Extraction "combinational_proof_tutorial.ml" prog.
