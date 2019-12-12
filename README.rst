=========================================================
 |koika|: A Core Language for Rule-Based Hardware Design
=========================================================

This is the home of |koika|, an experimental hardware design language inspired by `BlueSpec SystemVerilog <http://wiki.bluespec.com/>`_.  |koika| programs are built from *rules*, small bits of hardware that operate concurrently to compute state updates but provide `the illusion of serializable (atomic) updates <atomic-actions>`_.  |koika| has simple, precise semantics that give you `strong guarantees about the behavior of your designs <oraat>`_.

Our distribution includes an `executable reference implementation of the language <formal-semantics>`_ written using the `Coq proof assistant <coq>`_, machine-checked proofs ensuring that |koika|'s semantics are compatible with `one-rule-at-a-time execution <oraat>`_, and a `formally-verified compiler <compiler-verification>`_ that generates circuits guaranteed to correctly implement your designs.

|koika| programs are typically written inside of Coq using an `embedded DSL <syntax>`_ (this lets you leverage Coq's powerful metaprogramming features and modular abstractions), though we also have a more limited `standalone front-end <lispy-verilog>`_ that accepts programs in serialized (s-expressions) form.  For simulation, debugging, and testing purposes, |koika| programs can be compiled into `readable, cycle-accurate C++ models <cuttlesim>`_, and for synthesis the |koika| compiler targets a minimal subset of synthesizable Verilog supported by all major downstream tools.

|koika| is a research prototype: the circuits that our compiler generates typically have reasonable-to-good performance, but area usage is still very much a work in progress.  Because our simulator can take advantage of high-level information, |koika| designs typically run reasonably fast in C++ simulation.

Our largest example at the moment is a simple RISCV (RV32I) `4-stage pipelined core <examples/rv/RVCore.v>`_.

|koika| is currently developed as a joint research effort at MIT, involving members of CSG (the Computation Structure Group) and PLV (the Programming Languages & Verification group).  Our `latest draft <koika-paper>`_ is a good place to get details about the research that powers it.  The name “|koika|” (甲イカ) is Japanese for “`cuttlefish <https://en.wikipedia.org/wiki/Cuttlefish>`_”; we chose it because cuttlefishes have blue blood (a tribute to the name Bluespec), and because each of their eight arms are equipped with independent neurons that allow them operate semi-independently towards a shared purpose, much like rules in |koika| designs.

Getting started
===============

Dependencies
------------

* OCaml, `opam <https://opam.ocaml.org/doc/Install.html>`_, and ``make``.

* Coq 8.9 or later::

    opam install coq

* Coq's Ltac2 plugin, which will ship with Coq by default in 8.11::

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam install coq-ltac2

* Some OCaml packages::

    opam install dune base core stdio parsexp hashcons zarith

Building
--------

You can compile the full distribution, including examples, tests, and proofs by running ``make`` in the top-level directory of this repo.

Browsing examples
-----------------

The ``examples/`` directory of this repo demonstrates many of |koika|'s features.
The examples can be compiled using ``make examples``, and browsed in either
CoqIDE or Proof General.  There is basic Emacs support for ``.lv`` files (the “Lispy
Verilog” alternative frontend for |koika|) in ``etc/lv-mode.el``.

Compiling your own programs
---------------------------

**Programs written in the Coq EDSL**:
  On the Coq side, after implementing your design, use the following to define a “package”:

  .. code:: coq

     Definition package :=
       Interop.Backends.register
         {| ip_koika := …;
            ip_sim := …;
            ip_verilog := … |}.
     Extraction "xyz.ml" package.

  Compile your Coq sources using ``coqc`` or ``dune`` to generate ``xyz.ml``, then compile that file using ``cuttlec xyz.ml -T …``.

**Programs written in serialized syntax (“Lispy Verilog”)**:
  Use ``cuttlec your-program.lv -T verilog``, or any other output option as described by ``cuttlec --help``.

Technical details
=================

.. _koika-paper:

Details about |koika|\ 's design and implementation can be found in our `research paper <https://pit-claudel.fr/clement/papers/koika.pdf>`_.

Execution model
---------------

.. _atomic-actions:

|koika| programs are made of *rules*, orchestrated by a *scheduler*.  Each rule is a program that runs once per cycle, as long as it does not conflict with other rules.  When conflicts arise (for example, when two rules attempt to write to the same register), the priority order specified by the scheduler determines which rule gets to fire (i.e. execute).  Concretely, a rule might look like this (this is a rule that takes one step towards computing the GCD of the numbers in registers ``gcd_a`` and ``gcd_b``):

.. code:: coq

   let a := read0(gcd_a) in
   let b := read0(gcd_b) in
   if a != |16`d0| then
     if a < b then
       write0(gcd_b, a);
       write0(gcd_a, b)
     else
       write0(gcd_a, a - b)
   else
     fail

.. _oraat:

The semantics of |koika| guarantee that each rule executes atomically, and that generated circuits behave one-rule-at-a-time — that is, even when multiple rules fire in the same cycle, the updates that they compute are as if only one rule had run per cycle.  For example, consider the following rules:

.. _koika-syntax:

Syntax
------

|koika| programs are written using an embedded DSL inside of the Coq proof assistant.  After compiling the distribution, begin your file with ``Require Import Koika.Frontend``.

Preamble
~~~~~~~~

Start by defining the following types:

- ``reg_t``: An enumerated type describing the state of your machine.  For example,

  .. code:: coq

     Inductive reg_t :=
     (* These bypassing FIFOs are used to communicate with the memory *)
     | to_memory (state: MemReqFIFO.reg_t)
     | from_memory (state: MemRespFIFO.reg_t)
     (* These FIFOs are used to connect pipeline stages *)
     | d2e (state: fromDecodeFIFO.reg_t)
     | e2w (state: fromExecuteFIFO.reg_t)
     (* The register file and the scoreboard track and record reads and writes *)
     | register_file (state: Rf.reg_t)
     | scoreboard (state: Scoreboard.reg_t)
     (* These are plain registers, not modules *)
     | pc
     | epoch.

- ``ext_fn_t``: An enumerated type describing custom combinational primitives (custom IP) that your program should have access to (custom sequential IP is implemented using external rules, which are currently a work in progress; see `<examples/rv/RVCore.v>`_ for a concrete example).  For example,

  .. code::

     Inductive ext_fn_t :=
     | custom_adder (size: nat).

Then, declare the types of the data held in each part of your state, the initial value of each state element (we usually name these functions ``R`` and ``r``), and the signatures of your external (combinational) IP.  (In addition to bitsets, registers can contain structures, enums, or arrays of values; examples of these are given below.)

.. code:: coq

   Definition R (reg: reg_t) :=
     match reg with
     (* The type of the other modules is opaque; it's defined by the Rf module *)
     | to_memory st => MemReqFIFO.R st
     | register_file st => Rf.R st
     …
     (* Our own state is described explicitly: *)
     | pc => bits_t 32
     | epoch => bits_t 1
     end.

.. code:: coq

   Definition r (reg: reg_t) : R reg :=
     match reg with
     | to_memory st => MemReqFIFO.r st
     | register_file st => Rf.r st
     …
     | pc => Bits.zero
     | epoch => Bits.zero
     end.

.. code::

   Definition Sigma (fn: ext_fn_t) : ExternalSignature :=
     match fn with
     | custom_adder sz => {$ bits_t sz ~> bits_t sz ~> bits_t sz $}
     end.

Optionally, for reasoning purposes, you can give a Coq model of the external functions that you use:

.. code::

   Definition sigma (fn: ext_fn_t) : Sig_denote (Sigma fn) :=
     match fn with
     | custom_adder sz => fun (bs1 bs2: bits sz) => Bits.plus bs1 bs2
     end.

Finally, as needed, you can define your own custom types; here are a few examples:

.. code:: coq

   Definition proto :=
     {| enum_name := "protocol";
        enum_members :=
          vect_of_list ["ICMP"; "IGMP"; "TCP"; "UDP"];
        enum_bitpatterns :=
          vect_of_list [Ob~0~0~0~0~0~0~0~1; Ob~0~0~0~0~0~0~1~0;
                        Ob~0~0~0~0~0~1~1~0; Ob~0~0~0~1~0~0~0~1] |}.

.. code:: coq

   Definition flag :=
     {| enum_name := "flag";
        enum_members := vect_of_list ["set"; "unset"];
        enum_bitpatterns := vect_of_list [Ob~1; Ob~0] |}.

.. code:: coq

   Definition ipv4_address :=
     {| array_len := 4;
        array_type := bits_t 8 |}.

.. code:: coq

   Definition ipv4_header :=
     {| struct_name := "ipv4_header";
        struct_fields :=
          [("version", bits_t 4);
           ("ihl", bits_t 4);
           ("dscp", bits_t 6);
           ("ecn", bits_t 2);
           ("len", bits_t 16);
           ("id", bits_t 16);
           ("reserved", enum_t flag);
           ("df", enum_t flag);
           ("mf", enum_t flag);
           ("fragment_offset", bits_t 13);
           ("ttl", bits_t 8);
           ("protocol", enum_t proto);
           ("checksum", bits_t 16);
           ("src", array_t ipv4_address);
           ("dst", array_t ipv4_address)] |}.

.. code:: coq

   Definition result (a: type) :=
     {| struct_name := "result";
        struct_fields := [("valid", bits_t 1); ("value", a)] |}.

   Definition response := result (struct_t ipv4_header).

Rules
~~~~~

The main part of your program is rules.  You have access to the following syntax (there is no distinction between expressions and statements; statements are just expressions returning unit):

``pass``:
  Do nothing
``fail``:
  Abort the current rule, reverting all state changes
``let var := val in body``
  Let bindings
``set var := val``
  Assignments
``stmt1; stmt2``
  Sequence
``if val then val1 else val2``
  Conditional
``match val with  | pattern => body…  return default: body``
  Switches (case analysis)
``read0(reg)``, ``read1(reg)``, ``write0(reg)``, ``write1(reg)``
  Read or write a register at port 0 or 1
``pack(val)``, ``unpack(type, val)``
  Pack a value (go from struct, enum, or arrays to bits) or unpack a bitset
``get(struct, field)``, ``subst(struct, field, value)``
  Get a field of a struct value, or replace a field in a struct value (without mutating the original one)
``getbits(struct, field)``, ``substbits(struct, field, value)``
  Like get and subst, but on packed bitsets
``Ob~1~0~1~0``, ``|4`d10|``
  Bitset constants (here, the number 10 on 4 bits)
``struct name {| field_n := val_n;… |}``
  Struct constants
``enum name {| member |}``
  Enum constants
``!x``, ``x && y``, ``x || y``, ``x ^ y``
  Logical operators (not, and, or, xor)
``x + y``, ``x - y``, ``x << y``, ``x >> y``, ``x >>> y``
  Arithmetic operators (plus, minus, logical shits, arithmetic shift right)
``x < y``, ``x <s y``, ``x > y``, ``x >s y``, ``x <= y``, ``x <s= y``, ``x >= y``, ``x >s= y``, ``x == y``, ``x != y``
  Comparison operators, signed and unsigned
``x ++ y``, ``x[y]``, ``x[y :+ z]``
  Bitset operators (concat, select, indexed part-select)
``reg.(method)(arg, …)``
  Call a method of a module
``function(args…)``
  Call an internal function
``extcall function(args…)``
  Call an external function (combinational IP)

For example, the following rule decreases the ``ttl`` field of an ICMP packet:

.. code:: coq

   Definition _decr_icmp_ttl : uaction _ empty_ext_fn_t := {{
     let hdr := unpack(struct_t ipv4_header, read0(input)) in
     let valid := Ob~1 in
     match get(hdr, protocol) with
     | enum proto {| ICMP |} =>
       let t := get(hdr, ttl) in
       if t == |8`d0| then
         set valid := Ob~0
       else
         set hdr := subst(hdr, ttl, t - |8`d1|)
     return default: fail
     end;
     write0(output, pack(struct response {| valid := valid; value := hdr |}))
   }}.

This rule fetches the next instruction in our RV32I core:

.. code:: coq


   Definition fetch : uaction reg_t empty_ext_fn_t := {{
     let pc := read1(pc) in
     let req := struct mem_req {|
                           byte_en := |4`d0|; (* Load *)
                           addr := pc;
                           data := |32`d0| |} in
     let fetch_bookkeeping := struct fetch_bookkeeping {|
                                       pc := pc;
                                       ppc := pc + |32`d4|;
                                       epoch := read1(epoch)
                                     |} in
     toIMem.(MemReq.enq)(req);
     write1(pc, pc + |32`d4|);
     f2d.(fromFetch.enq)(fetch_bookkeeping)
   }}.


Functions
~~~~~~~~~

It is often convenient to separate out combination functions; for example:

.. code:: coq

   Definition alu32 : UInternalFunction reg_t empty_ext_fn_t := {{
     fun (funct3  : bits_t 3)
       (inst_30 : bits_t 1)
       (a       : bits_t 32)
       (b       : bits_t 32)
       : bits_t 32 =>
       let shamt := b[Ob~0~0~0~0~0 :+ 5] in
       match funct3 with
       | #funct3_ADD  => if (inst_30 == Ob~1) then a - b else a + b
       | #funct3_SLL  => a << shamt
       | #funct3_SLT  => zeroExtend(a <s b, 32)
       | #funct3_SLTU => zeroExtend(a < b, 32)
       | #funct3_XOR  => a ^ b
       | #funct3_SRL  => if (inst_30 == Ob~1) then a >>> shamt else a >> shamt
       | #funct3_OR   => a || b
       | #funct3_AND  => a && b
       return default: |32`d0|
       end
   }}.

.. _lispy-verilog:

.. _formal-semantics:

Formal semantics
----------------

.. _compiler-verification:

Compiler verification
---------------------

.. _cuttlesim:

Simulation
----------

Browsing the sources
====================

The following list shows the current state of the repo:

.. begin repo architecture

``coq/``
   - |coq/CircuitCorrectness.v|_: Circuits | Compiler correctness proof
   - |coq/CircuitProperties.v|_: Circuits | Lemmas used in the compiler-correctness proof
   - |coq/Circuits.v|_: Circuits | Syntax, semantics, compilation, and optimization of circuits
   - |coq/Common.v|_: Utilities | Shared utilities
   - |coq/DeriveShow.v|_: Utilities | Automatic derivation of Show instances
   - |coq/Desugaring.v|_: Frontend | Desugaring of untyped actions
   - |coq/Environments.v|_: Utilities | Environments used to track variable bindings
   - |coq/EqDec.v|_: Utilities | Decidable equality typeclass
   - |coq/ErrorReporting.v|_: Frontend | Typechecking errors and error-reporting functions
   - |coq/Extraction.v|_: Interop | Extraction to OCaml (compiler and utilities)
   - |coq/ExtractionSetup.v|_: Interop | Custom extraction settings (also used by external |koika| programs
   - |coq/FiniteType.v|_: Utilities | Finiteness typeclass
   - |coq/Frontend.v|_: Frontend | Top-level module imported by |koika| programs
   - |coq/IdentParsing.v|_: Frontend | Ltac2-based identifier parsing for prettier notations
   - |coq/IndexUtils.v|_: Utilities | Functions on Vect.index elements
   - |coq/Interop.v|_: Interop | Exporting |koika| programs for use with the cuttlec command-line tool
   - |coq/Member.v|_: Utilities | Dependent type tracking membership into a list
   - |coq/OneRuleAtATime.v|_: ORAAT | Proof of the One-rule-at-a-time theorem
   - |coq/Parsing.v|_: Frontend | Parser for the |koika| EDSL
   - |coq/PrimitiveProperties.v|_: Equations showing how to implement functions on structures and arrays as bitfuns
   - |coq/Primitives.v|_: Language | Combinational primitivies available in all |koika| programs
   - |coq/SemanticProperties.v|_: ORAAT | Properties of the semantics used in the one-rule-at-a-time theorem
   - |coq/Semantics.v|_: Language | Semantics of typed |koika| programs
   - |coq/Show.v|_: Utilities | Show typeclass (α → string)
   - |coq/Std.v|_: Stdlib | Standard library
   - |coq/Syntax.v|_: Frontend | Untyped syntax
   - |coq/SyntaxMacros.v|_: Frontend | Macros used in untyped programs
   - |coq/TypeInference.v|_: Frontend | Type inference and typechecking
   - |coq/TypedSyntax.v|_: Language | Typed ASTs
   - |coq/TypedSyntaxProperties.v|_: Tools | Lemmas pertaining to tools on typed syntax
   - |coq/TypedSyntaxTools.v|_: Tools | Functions defined on typed ASTs
   - |coq/Types.v|_: Language | Types used by |koika| programs
   - |coq/UntypedSyntaxTools.v|_: Frontend | Functions on untyped ASTs, including error localization
   - |coq/Vect.v|_: Utilities | Vectors and bitvector library

``examples/``
   ``rv/``
      ``etc/``
         - |examples/rv/etc/rvcore.cuttlesim.cpp|_: C++ driver for rv32i simulation with cuttlesim
         - |examples/rv/etc/rvcore.verilator.cpp|_: C++ driver for rv32i simulation with Verilator

      - |examples/rv/RVCore.v|_: Implementation of our RISC-V core
      - |examples/rv/RVEncoding.v|_: Encoding-related constants
      - |examples/rv/Scoreboard.v|_: Implementation of a scoreboard
      - |examples/rv/rv32i_core_pipelined.v|_: Pipelined instantiation of the core

   - |examples/collatz.lv|_: Computing terms of the Collatz sequence (Lispy Verilog version)
   - |examples/collatz.v|_: Computing terms of the Collatz sequence (Coq version)
   - |examples/datatypes.v|_: Using structures, enums, and arrays
   - |examples/external_rule.v|_: Calling external (verilog) modules from |koika|
   - |examples/function_call.v|_: Calling external functions
   - |examples/gcd_machine.v|_: Computing GCDs
   - |examples/method_call.v|_: Calling methods of internal modules
   - |examples/pipeline.v|_: Building simple pipelines
   - |examples/vector.v|_: Representing vectors of registers using Coq inductives

``ocaml/``
   ``backends/``
      ``resources/``
         - |ocaml/backends/resources/cuttlesim.hpp|_: Preamble shared by all |koika| programs compiled to C++

      - |ocaml/backends/coq.ml|_: Coq backend (from Lispy Verilog sources)
      - |ocaml/backends/cpp.ml|_: C++ backend
      - |ocaml/backends/dot.ml|_: Graphviz backend
      - |ocaml/backends/gen.ml|_: Embed resources/* into resources.ml at build time
      - |ocaml/backends/makefile.ml|_: Makefile backend (to make it easier to generate traces, statistics, models, etc.)
      - |ocaml/backends/verilator.ml|_: Verilator backend exporting a simple C++ driver
      - |ocaml/backends/verilog.ml|_: Verilog backend

   ``common/``
      - |ocaml/common/common.ml|_: Shared utilities

   ``cuttlebone/``
      - |ocaml/cuttlebone/cuttlebone.ml|_: OCaml wrappers around functionality provided by the library extracted from Coq

   ``frontends/``
      - |ocaml/frontends/coq.ml|_: Simple frontend to compile and load OCaml files extracted from Coq
      - |ocaml/frontends/lv.ml|_: Lispy Verilog frontend

   - |ocaml/cuttlec.ml|_: Command line interface to the compilers
   - |ocaml/interop.ml|_: Functions to use if compiling |koika| programs straight from Coq, without going through cuttlec
   - |ocaml/koika.ml|_: Top-level library definition
   - |ocaml/registry.ml|_: Stub used to load |koika| programs extracted from Coq into cuttlec

``tests/``
   - |tests/arrays.lv|_: Unit tests for array functions
   - |tests/bigint.lv|_: Computations with large bitvectors (the simulator uses boost for >64 bits)
   - |tests/comparisons.lv|_: Unit tests for comparison operators
   - |tests/datatypes.lv|_: Simple uses of structs and enums
   - |tests/double_write.v|_: Double-write detection and prevention
   - |tests/errors.1.lv|_: Syntax and typing errors in LV
   - |tests/errors.v|_: Syntax and typing errors in Coq
   - |tests/extcall.v|_: External functions
   - |tests/large_trace.lv|_: Make sure that snapshots in large traces don't copy data
   - |tests/large_writeset.v|_: Make sure that the large writeset heuristics in the scheduler don't break things
   - |tests/name_mangling.lv|_: Unit tests for name mangling
   - |tests/register_file_bypassing.v|_: Ensure that area is reasonable when bypasses don't need extra tracking
   - |tests/shadowing.lv|_: Unit tests for name shadowing
   - |tests/signed.lv|_: Computations involving sign bits
   - |tests/switches.v|_: Test various forms of switches
   - |tests/taint_analysis.lv|_: Unit tests to ensure that impure functions are not optimized out
   - |tests/unpack.v|_: Structure unpacking


.. |coq/CircuitCorrectness.v| replace:: ``CircuitCorrectness.v``
.. _coq/CircuitCorrectness.v: coq/CircuitCorrectness.v
.. |coq/CircuitProperties.v| replace:: ``CircuitProperties.v``
.. _coq/CircuitProperties.v: coq/CircuitProperties.v
.. |coq/Circuits.v| replace:: ``Circuits.v``
.. _coq/Circuits.v: coq/Circuits.v
.. |coq/Common.v| replace:: ``Common.v``
.. _coq/Common.v: coq/Common.v
.. |coq/DeriveShow.v| replace:: ``DeriveShow.v``
.. _coq/DeriveShow.v: coq/DeriveShow.v
.. |coq/Desugaring.v| replace:: ``Desugaring.v``
.. _coq/Desugaring.v: coq/Desugaring.v
.. |coq/Environments.v| replace:: ``Environments.v``
.. _coq/Environments.v: coq/Environments.v
.. |coq/EqDec.v| replace:: ``EqDec.v``
.. _coq/EqDec.v: coq/EqDec.v
.. |coq/ErrorReporting.v| replace:: ``ErrorReporting.v``
.. _coq/ErrorReporting.v: coq/ErrorReporting.v
.. |coq/Extraction.v| replace:: ``Extraction.v``
.. _coq/Extraction.v: coq/Extraction.v
.. |coq/ExtractionSetup.v| replace:: ``ExtractionSetup.v``
.. _coq/ExtractionSetup.v: coq/ExtractionSetup.v
.. |coq/FiniteType.v| replace:: ``FiniteType.v``
.. _coq/FiniteType.v: coq/FiniteType.v
.. |coq/Frontend.v| replace:: ``Frontend.v``
.. _coq/Frontend.v: coq/Frontend.v
.. |coq/IdentParsing.v| replace:: ``IdentParsing.v``
.. _coq/IdentParsing.v: coq/IdentParsing.v
.. |coq/IndexUtils.v| replace:: ``IndexUtils.v``
.. _coq/IndexUtils.v: coq/IndexUtils.v
.. |coq/Interop.v| replace:: ``Interop.v``
.. _coq/Interop.v: coq/Interop.v
.. |coq/Member.v| replace:: ``Member.v``
.. _coq/Member.v: coq/Member.v
.. |coq/OneRuleAtATime.v| replace:: ``OneRuleAtATime.v``
.. _coq/OneRuleAtATime.v: coq/OneRuleAtATime.v
.. |coq/Parsing.v| replace:: ``Parsing.v``
.. _coq/Parsing.v: coq/Parsing.v
.. |coq/PrimitiveProperties.v| replace:: ``PrimitiveProperties.v``
.. _coq/PrimitiveProperties.v: coq/PrimitiveProperties.v
.. |coq/Primitives.v| replace:: ``Primitives.v``
.. _coq/Primitives.v: coq/Primitives.v
.. |coq/SemanticProperties.v| replace:: ``SemanticProperties.v``
.. _coq/SemanticProperties.v: coq/SemanticProperties.v
.. |coq/Semantics.v| replace:: ``Semantics.v``
.. _coq/Semantics.v: coq/Semantics.v
.. |coq/Show.v| replace:: ``Show.v``
.. _coq/Show.v: coq/Show.v
.. |coq/Std.v| replace:: ``Std.v``
.. _coq/Std.v: coq/Std.v
.. |coq/Syntax.v| replace:: ``Syntax.v``
.. _coq/Syntax.v: coq/Syntax.v
.. |coq/SyntaxMacros.v| replace:: ``SyntaxMacros.v``
.. _coq/SyntaxMacros.v: coq/SyntaxMacros.v
.. |coq/TypeInference.v| replace:: ``TypeInference.v``
.. _coq/TypeInference.v: coq/TypeInference.v
.. |coq/TypedSyntax.v| replace:: ``TypedSyntax.v``
.. _coq/TypedSyntax.v: coq/TypedSyntax.v
.. |coq/TypedSyntaxProperties.v| replace:: ``TypedSyntaxProperties.v``
.. _coq/TypedSyntaxProperties.v: coq/TypedSyntaxProperties.v
.. |coq/TypedSyntaxTools.v| replace:: ``TypedSyntaxTools.v``
.. _coq/TypedSyntaxTools.v: coq/TypedSyntaxTools.v
.. |coq/Types.v| replace:: ``Types.v``
.. _coq/Types.v: coq/Types.v
.. |coq/UntypedSyntaxTools.v| replace:: ``UntypedSyntaxTools.v``
.. _coq/UntypedSyntaxTools.v: coq/UntypedSyntaxTools.v
.. |coq/Vect.v| replace:: ``Vect.v``
.. _coq/Vect.v: coq/Vect.v
.. |examples/collatz.lv| replace:: ``collatz.lv``
.. _examples/collatz.lv: examples/collatz.lv
.. |examples/collatz.v| replace:: ``collatz.v``
.. _examples/collatz.v: examples/collatz.v
.. |examples/datatypes.v| replace:: ``datatypes.v``
.. _examples/datatypes.v: examples/datatypes.v
.. |examples/external_rule.v| replace:: ``external_rule.v``
.. _examples/external_rule.v: examples/external_rule.v
.. |examples/function_call.v| replace:: ``function_call.v``
.. _examples/function_call.v: examples/function_call.v
.. |examples/gcd_machine.v| replace:: ``gcd_machine.v``
.. _examples/gcd_machine.v: examples/gcd_machine.v
.. |examples/method_call.v| replace:: ``method_call.v``
.. _examples/method_call.v: examples/method_call.v
.. |examples/pipeline.v| replace:: ``pipeline.v``
.. _examples/pipeline.v: examples/pipeline.v
.. |examples/rv/RVCore.v| replace:: ``RVCore.v``
.. _examples/rv/RVCore.v: examples/rv/RVCore.v
.. |examples/rv/RVEncoding.v| replace:: ``RVEncoding.v``
.. _examples/rv/RVEncoding.v: examples/rv/RVEncoding.v
.. |examples/rv/Scoreboard.v| replace:: ``Scoreboard.v``
.. _examples/rv/Scoreboard.v: examples/rv/Scoreboard.v
.. |examples/rv/etc/rvcore.cuttlesim.cpp| replace:: ``rvcore.cuttlesim.cpp``
.. _examples/rv/etc/rvcore.cuttlesim.cpp: examples/rv/etc/rvcore.cuttlesim.cpp
.. |examples/rv/etc/rvcore.verilator.cpp| replace:: ``rvcore.verilator.cpp``
.. _examples/rv/etc/rvcore.verilator.cpp: examples/rv/etc/rvcore.verilator.cpp
.. |examples/rv/rv32i_core_pipelined.v| replace:: ``rv32i_core_pipelined.v``
.. _examples/rv/rv32i_core_pipelined.v: examples/rv/rv32i_core_pipelined.v
.. |examples/vector.v| replace:: ``vector.v``
.. _examples/vector.v: examples/vector.v
.. |ocaml/backends/coq.ml| replace:: ``coq.ml``
.. _ocaml/backends/coq.ml: ocaml/backends/coq.ml
.. |ocaml/backends/cpp.ml| replace:: ``cpp.ml``
.. _ocaml/backends/cpp.ml: ocaml/backends/cpp.ml
.. |ocaml/backends/dot.ml| replace:: ``dot.ml``
.. _ocaml/backends/dot.ml: ocaml/backends/dot.ml
.. |ocaml/backends/gen.ml| replace:: ``gen.ml``
.. _ocaml/backends/gen.ml: ocaml/backends/gen.ml
.. |ocaml/backends/makefile.ml| replace:: ``makefile.ml``
.. _ocaml/backends/makefile.ml: ocaml/backends/makefile.ml
.. |ocaml/backends/resources/cuttlesim.hpp| replace:: ``cuttlesim.hpp``
.. _ocaml/backends/resources/cuttlesim.hpp: ocaml/backends/resources/cuttlesim.hpp
.. |ocaml/backends/verilator.ml| replace:: ``verilator.ml``
.. _ocaml/backends/verilator.ml: ocaml/backends/verilator.ml
.. |ocaml/backends/verilog.ml| replace:: ``verilog.ml``
.. _ocaml/backends/verilog.ml: ocaml/backends/verilog.ml
.. |ocaml/common/common.ml| replace:: ``common.ml``
.. _ocaml/common/common.ml: ocaml/common/common.ml
.. |ocaml/cuttlebone/cuttlebone.ml| replace:: ``cuttlebone.ml``
.. _ocaml/cuttlebone/cuttlebone.ml: ocaml/cuttlebone/cuttlebone.ml
.. |ocaml/cuttlec.ml| replace:: ``cuttlec.ml``
.. _ocaml/cuttlec.ml: ocaml/cuttlec.ml
.. |ocaml/frontends/coq.ml| replace:: ``coq.ml``
.. _ocaml/frontends/coq.ml: ocaml/frontends/coq.ml
.. |ocaml/frontends/lv.ml| replace:: ``lv.ml``
.. _ocaml/frontends/lv.ml: ocaml/frontends/lv.ml
.. |ocaml/interop.ml| replace:: ``interop.ml``
.. _ocaml/interop.ml: ocaml/interop.ml
.. |ocaml/koika.ml| replace:: ``koika.ml``
.. _ocaml/koika.ml: ocaml/koika.ml
.. |ocaml/registry.ml| replace:: ``registry.ml``
.. _ocaml/registry.ml: ocaml/registry.ml
.. |tests/arrays.lv| replace:: ``arrays.lv``
.. _tests/arrays.lv: tests/arrays.lv
.. |tests/bigint.lv| replace:: ``bigint.lv``
.. _tests/bigint.lv: tests/bigint.lv
.. |tests/comparisons.lv| replace:: ``comparisons.lv``
.. _tests/comparisons.lv: tests/comparisons.lv
.. |tests/datatypes.lv| replace:: ``datatypes.lv``
.. _tests/datatypes.lv: tests/datatypes.lv
.. |tests/double_write.v| replace:: ``double_write.v``
.. _tests/double_write.v: tests/double_write.v
.. |tests/errors.1.lv| replace:: ``errors.1.lv``
.. _tests/errors.1.lv: tests/errors.1.lv
.. |tests/errors.v| replace:: ``errors.v``
.. _tests/errors.v: tests/errors.v
.. |tests/extcall.v| replace:: ``extcall.v``
.. _tests/extcall.v: tests/extcall.v
.. |tests/large_trace.lv| replace:: ``large_trace.lv``
.. _tests/large_trace.lv: tests/large_trace.lv
.. |tests/large_writeset.v| replace:: ``large_writeset.v``
.. _tests/large_writeset.v: tests/large_writeset.v
.. |tests/name_mangling.lv| replace:: ``name_mangling.lv``
.. _tests/name_mangling.lv: tests/name_mangling.lv
.. |tests/register_file_bypassing.v| replace:: ``register_file_bypassing.v``
.. _tests/register_file_bypassing.v: tests/register_file_bypassing.v
.. |tests/shadowing.lv| replace:: ``shadowing.lv``
.. _tests/shadowing.lv: tests/shadowing.lv
.. |tests/signed.lv| replace:: ``signed.lv``
.. _tests/signed.lv: tests/signed.lv
.. |tests/switches.v| replace:: ``switches.v``
.. _tests/switches.v: tests/switches.v
.. |tests/taint_analysis.lv| replace:: ``taint_analysis.lv``
.. _tests/taint_analysis.lv: tests/taint_analysis.lv
.. |tests/unpack.v| replace:: ``unpack.v``
.. _tests/unpack.v: tests/unpack.v
.. end repo architecture

.. |koika| replace:: Kôika
