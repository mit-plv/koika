(*! Simple arithmetic (commented) !*)
Require Import Koika.Frontend.

(*|
===========================================================
 A simple arithmetic pipeline and its proof of correctness
===========================================================

In this file we model a simple arithmetic pipeline with two functions `f` and `g`::

  input --(f)--> queue --(g)--> output

For simplicity, ``input`` and ``output`` will be registers, and we'll update ``input`` at the end of each cycle using an external function ``NextInput`` (think of it as an oracle).

Our system will have two rules: ``doF`` and ``doG``, each corresponding to one step of the pipeline.

All that follows is parametrized on a register size ``sz``, set to 32 bits by default.
|*)

Definition sz := pow2 5.

(*|
Setup
=====

We start by defining the system using inductive types to declare its registers and rules and their types:
|*)

Inductive reg_t :=
| input_buffer (** The data source: inputs are read from this register *)
| queue_empty (** A flag indicating whether the queue is empty *)
| queue_data (** The data stored in the queue *)
| output_buffer. (** The data sink: outputs are written to this register *)

Definition R r :=
  match r with
  | input_buffer  => bits_t sz
  | queue_empty   => bits_t 1
  | queue_data    => bits_t sz
  | output_buffer => bits_t sz
  end.

Inductive ext_fn_t :=
| NextInput (** This function computes the next element of the input stream. **)
| F
| G.

Definition Sigma (fn: ext_fn_t) : ExternalSignature :=
  match fn with
  | NextInput => {$ bits_t sz ~> bits_t sz $}
  | F         => {$ bits_t sz ~> bits_t sz $}
  | G         => {$ bits_t sz ~> bits_t sz $}
  end.

(*|
Then we declare the rules of the system.  Notice how ``doG`` writes at port 0 and ``doF`` reads at port 1.  This is because we're building a pipelined queue, not a bypassing one, so we expect clients to pull first and push second.  Notice also that each rule is implicitly "guarded"; that is, if ``doF`` can't push into the queue because ``doG`` is lagging, or if there's no data ready for ``doG`` to
|*)

Definition _doF : uaction _ _ :=
  {{
     let v := read0(input_buffer) in
     write0(input_buffer, extcall NextInput(v));
     let queue_empty := read1(queue_empty) in
     if queue_empty then
       write1(queue_empty, Ob~0);
       write0(queue_data, extcall F(v))
     else
       fail
  }}.

Definition _doG : uaction _ _ :=
  {{
      let queue_empty := read0(queue_empty) in
      if !queue_empty then
        let data := read0(queue_data) in
        write0(output_buffer, extcall G(data));
        write0(queue_empty, Ob~1)
      else
        fail
  }}.

(*|
Rules are written in an untyped language, so we need to typecheck them, which is done using ``tc_rules``:
|*)

Inductive rule_name_t :=
| doF
| doG.

Definition rules :=
  Eval vm_compute in
    tc_rules R Sigma
             (fun rl => match rl with
                     | doF => _doF
                     | doG => _doG
                     end).

(*|
The last step if to define the system's scheduler.  Note that we perform ``doG`` before ``doF`` (intuitively, pipelines run back-to-front: in a sequential model, G removes the data found in the queue and writes it to the output, then F reads the input and writes it in the queue).
|*)

Definition pipeline : scheduler :=
  doG |> doF |> done.

(*|
That's it, we've defined our program!  There are a few things we can do with it now.

Running our program
===================

Kôika's semantics are deterministic, so we can simply run the program using the interpreter.  For this we need to define two provide two additional pieces: the value of the registers at the beginning of the cycle (``r``), and a model of the external functions (``sigma``).

For the registers, we start with an empty queue, the input set to 32'd1, and the output set to 32'd0.  The notation ``#{ reg => val #}`` indicates that register ``reg`` maps to value ``val``.  Notations like ``Ob~1~0~0~1`` denote bitstring constants: for example, ``Ob~0~1~1`` is the Kôika equivalent of ``3'b011`` in Verilog.
|*)

(** [reg_t] is finite; we need to know this to construct register maps. *)
Instance FiniteType_reg_t : FiniteType reg_t := _.

Definition r : ContextEnv.(env_t) R :=
  #{ input_buffer  => Bits.of_nat 32 1;
     queue_empty   => Ob~1;
     queue_data    => Bits.of_nat 32 0;
     output_buffer => Bits.of_nat 32 0 }#.

(*|
For the external functions, we take something simple: ``f`` multiplies its input by 5, ``g`` adds one to its input, and ``nextInput`` models the sequence of odd numbers ``1, 3, 5, 7, 9, …``:
|*)

Definition sigma fn : Sig_denote (Sigma fn) :=
  match fn with
  | NextInput => fun x => Bits.plus x (Bits.of_nat _ 2)
  | F         => fun x => Bits.slice 0 32 (Bits.mul x (Bits.of_nat 32 5))
  | G         => fun x => Bits.plus x (Bits.of_nat _ 1)
  end.

(*|
In the first step of execution ``doG`` does not execute and ``doF`` reads 1 from the input and writes 5 (32'b101) in the queue; the input then becomes 3 (32'b11).

The function ``interp_cycle`` computes this update: it returns a map of register values.
|*)

Compute (interp_cycle sigma rules pipeline r).

(*|
Here is an infinite stream capturing the initial state of the system and all snapshots of the system after each execution:
|*)

Definition system_states :=
  Streams.coiterate (TypedSemantics.interp_cycle sigma rules pipeline) r.

(* FIXME move me *)

(*|
Forcing this infinite stream simulates the whole system directly inside Coq: for example, we can easily extract the first few inputs that the system processes, and the first few outputs that it produces:

- Inputs (1; 3; 5; 7; 9; …):
  ..
|*)

Compute (Streams.firstn 5 (Streams.map (fun r => r.[input_buffer]) system_states)).
Compute (Streams.firstn 5 (Streams.map (fun r => @Bits.to_nat 32 r.[input_buffer]) system_states)).

(*|
- Outputs (1 * 5 + 1 = 6; 3 * 5 + 1 = 16; 5 * 5 + 1 = 26; …); the first two zeros correspond pipeline's initial lag (the first 0 is the initial state; the second, the result of running one cycle; after that, the output is updated at every cycle):
  ..
|*)

Compute (Streams.firstn 5 (Streams.map (fun r => r.[output_buffer]) system_states)).
Compute (Streams.firstn 5 (Streams.map (fun r => @Bits.to_nat 32 r.[output_buffer]) system_states)).

(*|
Simulating this way is convenient for exploring small bits of code; for large designs, we have a compiler that generates optimized (but readable!) C++ that simulates Kôika designs 4 to 5 orders of magnitude faster than running directly in Coq does (a small example like this one runs hundreds of millions of simulated cycles per second in C++, and thousands in Coq):
|*)

Time Compute (@Bits.to_nat 32 (Streams.Str_nth 1000 system_states).[output_buffer]).

(*|
Running individual rules
------------------------

We can also simulate at finer granularity: for example, here is what happens for each rule during the first cycle (each step produces a log of events that happen as part of this rule's execution):

- ``doG`` fails, because the queue is empty:
  ..
|*)

Compute (TypedSemantics.interp_rule r sigma log_empty (rules doG)).

(*|
- ``doF`` succeeds and updates the queue and the input buffer:
  ..
|*)

Compute (TypedSemantics.interp_rule r sigma log_empty (rules doF)).

(*|
In later cycles (here, cycle 3), ``doG`` succeeds as well and writes 1 to (port 0 of) ``queue_empty``…
|*)

Compute (let r := Streams.Str_nth 3 system_states in
         TypedSemantics.interp_rule r sigma log_empty (rules doG)).

(*|
… and ``doF`` sets (port 1 of) ``queue_empty`` back to 0 as it refills the queue:
|*)

Compute (let r := Streams.Str_nth 3 system_states in
         let logG := TypedSemantics.interp_rule r sigma log_empty (rules doG) in
         TypedSemantics.interp_rule r sigma (must logG) (rules doF)).

(*|
Generating circuits
===================

Generating a circuit is just a matter of calling the compiler, which is a Gallina function too:
|*)

(** ``external`` is an escape latch used to inject arbitrary Verilog into a
    design; we don't use it here **)
Definition external (r: rule_name_t) := false.

Definition circuits :=
  compile_scheduler rules external pipeline.

(*|
For printing circuits, we don't recomment using Coq's ``Compute``: our representation of circuits uses physical equality to track shared subcircuits, but Coq's printer doesn't respect sharing when printing, and hence generated circuits look giant.  Instead, we recommend looking at the generated Verilog or Dot graphs (use ``make examples/_objects/pipeline.v``).

We can, however, easily compute the results produced by a circuit, either after one cycle:
|*)

Compute (interp_circuits sigma circuits (lower_r r)).

(*|
… or after multiple cycles:
|*)

Definition circuit_states :=
  Streams.coiterate (interp_circuits sigma circuits) (lower_r r).

Compute (Streams.firstn 5 (Streams.map (fun r => r.[output_buffer]) circuit_states)).
Compute (Streams.firstn 5 (Streams.map (fun r => @Bits.to_nat 32 r.[output_buffer]) circuit_states)).

(*|
Proving properties
==================

The compiler is proven correct, so we know that runnign a circuit will always produce the same results as running the original Kôika design.  But we haven't proved anything yet about our Kôika design, so it could be full of bugs.  Here we're interested in ruling out two types of bugs: function correctness bugs and timing bugs.

The first class of bugs would cause our design to compute something different from `g ∘ f`.  The second class of bug would cause it to stuffer or lag, taking more than one cycle to produce each output.
|*)

Require Koika.CompactSemantics.
Section Correctness.

(*|
We start by quantifying over ``sigma``, the model of external functions.  This matters because we want to prove our design correct regarless of the concrete functions that we plug in:
|*)

  Context (sigma: forall f, Sig_denote (Sigma f)).

(*|
.. coq:: none
|*)

  Arguments id _ _ / : assert.
  Arguments env_t: simpl never.
  Arguments vect: simpl never.
  Arguments may_read /.
  Arguments may_write /.
  Opaque CompactSemantics.interp_cycle.

  (* FIXME remove these notations *)
  Notation "1'b0" := {| vhd := false; vtl := _vect_nil |}.
  Notation "1'b1" := {| vhd := true; vtl := _vect_nil |}.

  Import StreamNotations.

(*|
Let's start by stating a specification that will rule both kinds of bugs.  In this example we completely characterize the pipeline (we have examples that use weaker characterizations such as invariants, but we haven't written a tutorial for them yet).  Note how we quantify over ``r``: as we'll see later, our design will work for any strating state, as long as the queue starts empty.
|*)

  Section Spec.
    Context (r: ContextEnv.(env_t) R).

(*|
Here is the stream of inputs consumed by the spec: we just iterate ``nextInput`` on the original value ``r.[input_buffer]``.
|*)

    Definition spec_inputs :=
      Streams.coiterate (sigma NextInput) r.[input_buffer].

(*|
Here is the expected stream of outputs, which we call “observations”.  We only expect outputs to start becoming available after completing two cycles, so we simply state that the value in ``output_buffer`` should be unchanged until then:
|*)

    Definition spec_observations :=
      let composed x := sigma G (sigma F x) in
      r.[output_buffer] ::: r.[output_buffer] ::: Streams.map composed spec_inputs.

(*|
Here is the actual stream of states produced by the implementation, which we previously called “system_states”.  Note that we use the ``CompactSemantics`` module, which uses a more explicit representation of logs that plays more smoothly with abstract interpretation (instead of storing lists of events, it stores a record indicating whether we'ver read or written at port 0 and 1).

FIXME: use regular semantics and introduce compact ones in the proof.
|*)

    Definition impl_trace : Streams.Stream (ContextEnv.(env_t) R) :=
      Streams.coiterate (CompactSemantics.interp_cycle (R := R) sigma rules pipeline) r.

(*|
Finally, here is the actual stream of observations produced by the implementation:
|*)

    Definition impl_observations :=
      Streams.map (fun r: ContextEnv.(env_t) R => r.[output_buffer]) impl_trace.
  End Spec.

(*|
The approach we'll use in this proof is to give a complete characterization of two cycles of the pipeline, and then use k-induction for `k = 2` to generalize it into a complete characterization of the system for any number of cycles.  Here's how that looks:
|*)

  Section Proofs.

(*|
This definition captures what it means to execute one cycle:
|*)

    Definition cycle (r: ContextEnv.(env_t) R) :=
      CompactSemantics.interp_cycle (R := R) sigma rules pipeline r.

(*|
Here is our two-cycle characterization: if we execute our circuit twice, ``input_buffer`` takes two steps of ``nextInput``, ``queue_empty`` becomes false (regardless of where we start, the queue will be filled). ``queue_data`` contains ``f`` of the input updated by the first cycle, and ``output`` buffer contains the correct output.
|*)

    Definition phi2 (r: ContextEnv.(env_t) R)
      : ContextEnv.(env_t) R :=
      #{ input_buffer => sigma NextInput (sigma NextInput r.[input_buffer]);
         queue_empty => Ob~0;
         queue_data => sigma F (sigma NextInput r.[input_buffer]);
         output_buffer => sigma G (sigma F r.[input_buffer]) }#.

(*|
Proving this characterization is just a matter of abstract interpretation:
|*)

    Lemma phi2_correct :
      forall r, cycle (cycle r) = phi2 r.
    Proof.
      intros r; unfold cycle.

(*|
We start by unfolding the inner call to ``interp_cycle``, which yields a characterization that branches on ``r.[queue_empty]``:
|*)

      rewrite (interp_cycle_cps_correct_rev r); simpl.

(*|
Then we do a case split on ``r.[queue_empty]``, and we use abstract interpretation again to show that both ases lead to the same result:
|*)

      destruct (Bits.single r.[queue_empty]); simpl.
      all: rewrite interp_cycle_cps_correct_rev; simpl;
        reflexivity.
    Qed.

(*|
With this done, we can now prove a stronger characterization that holds for any number of cycles:
|*)

    Definition phi_iterated n
               (r: ContextEnv.(env_t) R)
      : ContextEnv.(env_t) R :=
      #{ input_buffer => iterate (S (S n)) (sigma NextInput) r.[input_buffer];
         queue_empty => Ob~0;
         queue_data => sigma F (iterate (S n) (sigma NextInput) r.[input_buffer]);
         output_buffer => sigma G (sigma F (iterate n (sigma NextInput) r.[input_buffer])) }#.

(*|
The proof is a two-induction (captured by the ``Div2.ind_0_1_SS`` lemma); it tells us what the registers contain after ``n + 2`` cycles of the pipeline:
|*)

    Lemma phi_iterated_correct :
      forall r n,
        iterate (S (S n)) cycle r =
        phi_iterated n r.
    Proof.
      intros r n.
      rewrite !iterate_S_acc, phi2_correct.
      revert n; apply Div2.ind_0_1_SS; simpl.
      - reflexivity.
      - unfold cycle; rewrite interp_cycle_cps_correct_rev; reflexivity.
      - intros n IH; simpl in IH; rewrite IH; reflexivity.
    Qed.

(*|
And this is enough to complete our proof!  We'll manually match up the first two states, then use our characterization:
|*)

    Theorem correct_pipeline:
      forall (r: ContextEnv.(env_t) R),
        r.[queue_empty] = Ob~1 ->
        Streams.EqSt (impl_observations r) (spec_observations r).
    Proof.
      intros r Hqueue_empty.
      unfold impl_observations, spec_observations, impl_trace.

      apply Streams.ntheq_eqst; intros [ | [ | n ] ]; simpl;
        unfold spec_inputs; rewrite ?Streams.Str_nth_0, ?Streams.Str_nth_S, ?Streams.Str_nth_map, ?Streams.Str_nth_coiterate.
      - (* Initial state *)
        simpl.
        reflexivity.
      - (* After one cycle *)
        simpl.
        rewrite interp_cycle_cps_correct_rev; simpl.
        rewrite Hqueue_empty; reflexivity.
      - (* After two cycles *)
        rewrite phi_iterated_correct.
        simpl.
        reflexivity.
    Qed.
  End Proofs.

  Section Experiments.
    Context (r: ContextEnv.(env_t) R).
    Import CompactSemantics.

    Lemma cycle_correct :
      forall (init: ContextEnv.(env_t) R),
      exists l', Logs.commit_update init (TypedSemantics.interp_scheduler init sigma rules pipeline) = l'.
    Proof.
      intros; unfold pipeline.
      Fail Timeout 1 Time unfold TypedSemantics.interp_scheduler, TypedSemantics.interp_scheduler', TypedSemantics.interp_rule; simpl. (* 11s *)
    Abort.

    Lemma cycle_correct :
      forall (init: ContextEnv.(env_t) R),
      exists l', CompactLogs.commit_update init (interp_scheduler init sigma rules pipeline) = l'.
    Proof.
      intros; unfold pipeline.
      Fail Timeout 1 Time unfold interp_scheduler, interp_scheduler', interp_rule; simpl. (* 10-15s *)
    Abort.

    (* FIXME things get slower if I let Coq infer the R *)

    Lemma cycle_correct :
      forall (init: ContextEnv.(env_t) R),
      exists l', CompactSemantics.interp_cycle (R := R) sigma rules pipeline init = l'.
    Proof.
      intros; unfold pipeline.
      apply wp_cycle_correct.
      Time simpl. (* 0.6s *)

      destruct (Bits.single init.[queue_empty]); simpl.
      - (* Initialization: nothing in the queue yet *)
        eexists; reflexivity.
      - (* Steady state: queue remains full *)
        eexists; reflexivity.
    Qed.

    Lemma scheduler_correct :
      exists l', CompactSemantics.interp_scheduler r sigma rules pipeline = l'.
    Proof.
      unfold pipeline.
      (* unfold interp_scheduler, interp_scheduler', interp_rule; simpl. *)
      (* rewrite <- interp_scheduler_cps_correct; simpl. *)
      apply wp_scheduler_correct.
      Time simpl.
      destruct (Bits.single (getenv ContextEnv r queue_empty)); simpl.
      all: eexists; reflexivity.
    Qed.

    Lemma scheduler_correct' :
      (interp_scheduler r sigma rules pipeline).[input_buffer].(lwrite1) = None.
    Proof.
      unfold pipeline.
      (* unfold CompactSemantics.interp_scheduler, CompactSemantics.interp_scheduler', CompactSemantics.interp_rule; simpl. *)
      (* rewrite <- interp_scheduler_cps_correct; simpl. *)
      apply wp_scheduler_correct.
      Time simpl.
      destruct (Bits.single (getenv ContextEnv r queue_empty)); simpl.
      all: eexists; reflexivity.
    Qed.

    Lemma doG_correct :
      Bits.single (r.[queue_empty]) = false ->
      exists l,
        CompactSemantics.interp_rule r sigma log_empty (rules doG) = Some l /\
        l.[queue_empty].(lwrite0) = Some Ob~1.
    (* FIXME: which style is better; exists or match? *)
    (* match CompactSemantics.interp_rule r sigma log_empty (rules doG) with *)
    (* | Some l => *)
    (*   l.[queue_empty] = [LE LogWrite P0 Ob~1; LE LogRead P0 tt] *)
    (* | None => False *)
    (* end. *)
    Proof.
      intros Hvalid.
      unfold CompactSemantics.interp_rule.
      (* Time simpl.  rewrite Hvalid; simpl; eexists; split; reflexivity. *)
      apply wp_action_correct.
      Time simpl; rewrite Hvalid; simpl; eexists; split; reflexivity.
    Qed.

    Arguments vect_cons: simpl never.
    Arguments env_t : simpl never.

    Ltac autorew :=
      (* The variant below isn't enough, because primitive projections are weird *)
      (* | [ H: ?a = _ |- _ ] => *)
      (*   match goal with (* Merging the two matches together results in a 20x slowdown *) *)
      (*   | [  |- context[a] ] => rewrite !H *)
      (*   end *)
      repeat match goal with
             | [ H: ?a = ?a' |- context[match ?b with _ => _ end] ] =>
               unify a b; replace b with a' by assumption
             end.               (* FIXME doesn't work here *)

    Arguments may_read0 /.
    Arguments may_write0 /.
    Arguments may_read1 /.
    Arguments may_write1 /.

    Lemma doF_correct :
      forall l,
        let l_input_buffer := l.[input_buffer] in
        let l_queue_empty := l.[queue_empty] in
        let l_queue_data := l.[queue_data] in
        l_input_buffer.(lwrite0) = None ->
        l_input_buffer.(lwrite1) = None ->
        l_input_buffer.(lread1) = false ->
        l_queue_data.(lread1) = false ->
        l_queue_data.(lwrite0) = None ->
        l_queue_data.(lwrite1) = None ->
        l_queue_empty.(lwrite1) = None ->
        l_queue_empty.(lwrite0) = Some Ob~1 ->
        (* r.[queue_data] = (sigma F) (r.[output_buffer]) -> *)
        exists l',
          CompactSemantics.interp_rule (R := R) r sigma l (rules doF) = Some l'.
    Proof.
      intros.
      unfold CompactSemantics.interp_rule.
      (* rewrite interp_action_cps_correct_rev. *)
      (* simpl. *)
      apply wp_action_correct.
      Time simpl.
      Time autorew.
      simpl.
      eexists; reflexivity.
    Qed.

    (* Compact encoding of preconditions *)
    Lemma doF_correct' :
      forall qd0 ob qe0 qe1 ib0,
        let l :=
            #{ input_buffer => {| lread0 := ib0; lread1 := false; lwrite0 := None; lwrite1 := None |};
               queue_empty => {| lread0 := qe0; lread1 := qe1; lwrite0 := Some Ob~1; lwrite1 := None |};
               queue_data => {| lread0 := qd0; lread1 := false; lwrite0 := None; lwrite1 := None |};
               output_buffer => ob }# in
        exists l', CompactSemantics.interp_rule r sigma l (rules doF) = Some l'.
    Proof.
      intros.
      unfold CompactSemantics.interp_rule.
      apply wp_action_correct.
      Time simpl.
      (* Nothing to rewrite! *)
      eexists; reflexivity.
    Qed.
  End Experiments.
End Correctness.

(*|
Extracting to Verilog and C++
=============================

For this final piece, we need to specify which C++ and Verilog functions ``F``, ``G``, and ``nextInput`` correspond to; we do so by constructing a ``package``, which contains all relevant information:
|*)

Definition cpp_extfuns := "class extfuns {
public:
  static bits<32> next_input(bits<32> st) {
    return st + bits<32>{2};
  }

  static bits<32> f(bits<32> x) {
    return prims::slice<0, 32>(x * bits<32>{5});
  }

  static bits<32> g(bits<32> x) {
    return x + bits<32>{1};
  }
};".

Definition ext_fn_names fn :=
  match fn with
  | NextInput => "next_input"
  | F => "f"
  | G => "g"
  end.

Definition package :=
  {| ip_koika := {| koika_reg_types := R;
                   koika_reg_init reg := r.[reg];
                   koika_ext_fn_types := Sigma;
                   koika_rules := rules;
                   koika_rule_external := external;
                   koika_scheduler := pipeline;
                   koika_module_name := "pipeline_tutorial" |};

     ip_sim := {| sp_ext_fn_specs fn :=
                   {| efs_name := ext_fn_names fn;
                      efs_method := false |};
                 sp_prelude := Some cpp_extfuns |};

     ip_verilog := {| vp_ext_fn_specs fn :=
                       {| efr_name := ext_fn_names fn;
                          efr_internal := true |} |} |}.

(*|
This last bit registers our program, which allows the build system to locate it:
|*)

Definition prog := Interop.Backends.register package.
Extraction "pipeline_tutorial.ml" prog.
