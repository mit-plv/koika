Kôika: A Core Language for Rule-Based Hardware Design
=====================================================

PLDI 2020 AEC
-------------

### Introduction

Thanks for reviewing this artifact! We hope that you'll find it easy to
use and evaluate.  A copy of the submitted paper is in the current
folder, under the name ‘~/pldi2020/paper.pdf’.

This virtual machine was set up using a Vagrant script; the entire configuration
can be replicated using the setup script at `koika/etc/vagrant/provision.sh` on
an Ubuntu 19.10 base.  The main README (`koika/README.html`) also provides
detailed setup instruction if you want to try running Kôika on your own machine.

### Contents

To support the claims of the paper, this artifact contains a snapshot of the
Kôika repository, including the following artifacts:

* An executable reference implementation of the language written in Coq
* Machine-checked proofs of the ORAAT theorem
* A formally-verified compiler
* Two cycle-equivalent RISCV cores, one written in BlueSpec and one in Kôika

The instructions below step you through these artifacts and include detailed
instructions to reproduce the results and figures of the paper.  The VM includes
Emacs with Proof-General and company-coq, as well as CoqIDE.

### Getting started

The `koika/` directory is organized as follows:

- `coq/`: Coq formalization and implementation of the language
- `examples/`: Simple kôika programs
- `examples/rv/`: A Kôika implementation of a RISC-V core
- `ocaml/`: Command line interface and RTL pretty-printer

This README is self-sufficient, but we expect you'll enjoy the experience more
if you read Kôika's main README (koika/README.rst) first (it's the one we use to
onboard new contributors!).  It also includes a much more detailed index of the
repository.

### First part: Mechanization and Verification

#### Semantics

The terms and semantics described in Section 3 of the paper correspond to the
`action` AST defined in `koika/coq/LoweredSyntax.v` and the interpreter defined
in `koika/coq/LoweredSemantics.v` (schedulers are defined in
`koika/coq/Syntax.v`).  In addition to the syntax described in the paper, our
Coq implementation includes support for internal function calls and assignments
to mutable variables, and we also have a more strongly typed AST with arrays,
enums, and structures, whose ASTs and semantics are defined in
`koika/coq/TypedSyntax.v` and `koika/coq/TypedSemantics.v`.

Our RTL semantics are formalized in `koika/coq/CircuitSyntax.v` and
`koika/coq/CircuitSemantics.v` (the Coq implementation includes a single
constructor for binary operators, as well as an additional constructor for calls
to external components).

#### Metatheory

The ORAAT theorem of Section 4 is stated and proven in
`koika/coq/OneRuleAtATime.v`.  The main theorem, `OneRuleAtATime`, says that
executing a scheduler in a single cycle and committing the resulting log is the
same as running each rule individually, one-by-one, committing the results
between each rule.

#### Compilation

Our compiler first lowers strongly typed ASTs into bit-manipulating (“lowered”)
programs, then generates circuits by applying the algorithm described in Section
6 of the paper, implemented in `koika/coq/CircuitGeneration.v`.  Circuit
optimizations are implemented in `koika/coq/CircuitOptimization.v`, including
optimizations added after the original submission which significantly reduce the
number of gates occupied by our RISCV processor.

You can see both semantics in action (in particular `interp_action`,
`interp_scheduler`, and `commit_update`), as well as the compiler, by stepping
through `koika/examples/collatz.v`, for example.

#### Compiler-correctness

Our top-level theorem is stated in `koika/coq/Correctness.v`.  It guarantees
that, given a scheduler and a set of register values, the value computed for
each register by `TypedSemantics.interp_scheduler` composed with `commit_update`
is the same as the value computed by `interp_circuit` when applied to the
circuits compiled from the original scheduler.

To recompile all Coq sources and check all proofs, use `make all` in
`koika/coq`.

### Second part: case study

#### Implementation

Our largest case-study is a simple RISCV CPU core, written in Kôika.  We use our
compiler to generate RTL circuits, which we pretty-print to Verilog, and from
there we use open-source synthesis tools to generate ASIC designs or FPGA
bitstreams.  For comparison, we also wrote a BlueSpec version of the core.

Before browsing the implementation of the core, we recommend familiarizing
yourself with Kôika's syntax using the README and simpler examples, such as
`koika/examples/collatz.v` and `koika/examples/gcd_machine.v`.

The file `koika/examples/rv/RVCore.v` contains the implementation of the
processor; each rule corresponds to one pipeline stage (the two special rules
`ExternalI` and `ExternalD` are replaced at compile time by a Verilog
implementation of an external BRAM device).  The file `koika/examples/rv/rv32.v`
contains the processor's scheduler.  To compile the procesor, run `make core` in
`koika/examples/rv`.

#### Experimental results

To run the rv32i test suite, as well as a collection of more complex
integration tests, run `make verilator-tests` in `koika/examples/rv/`.  These
tests are run using an open-source verilog simulator called Verilator.

To check that the Kôika implementation matches the baseline Bluespec core, use
the following two commands (each will take about 20 minutes to run the full
simulation):

- `PYVERILATOR_TOP=top.v make pyverilator-tests`: this prints cycle and
  instruction counts for the Kôika design.
- `PYVERILATOR_TOP=bsv/rv32_bsv/top_bsv.v make pyverilator-tests`: this prints
  cycle and instruction counts for the BlueSpec design.

These commands will take some time, and the instruction and cycle counts will
differ slightly from the paper (this is due to compiler variations).  However,
as claimed, the cycles counts will match; look for blocks like these:

    PASS
    [mandelbrot.vmh]@[top.v]:
    cycle_count: 32'b00000100001100111110000011011000 (0x433e0d8, 70508760)
    instr_count: 32'b00000010011101000011000001010000 (0x2743050, 41168976)
    real: 14m18,770s	user: 14m17,630s	sys: 0m0,273s

and

    PASS
    [mandelbrot.vmh]@[top_bsv.v]:
    cycle_count: 32'b00000100001100111110000011011000 (0x433e0d8, 70508760)
    rv_core_instr_count: 32'b00000010011101000011000001010000 (0x2743050, 41168976)
    real: 12m4,310s	user: 12m1,741s	sys: 0m0,245s

To obtain performance and area numbers, use `make nangate45-synthesis`.  This
script uses the open-source `Yosys` and `abc` tools to target the free 45nm Open
Cell library.  Thanks to the additional optimizations that we implemented after
submitting the paper, the Kôika implementation has much better gate counts than
originally reported, while retaining comparable performance.  The results should
look similar to the following:

    Kôika: ABC: WireLoad = "none"  Gates =  14634 ( 19.0 %)   Cap =  3.3 ff (  1.1 %)   Area =    14122.21 ( 93.6 %)   Delay =   684.09 ps  ( 14.2 %)
    BSV: ABC: WireLoad = "none"  Gates =  12310 ( 19.1 %)   Cap =  3.5 ff (  1.3 %)   Area =    11968.94 ( 93.1 %)   Delay =   649.63 ps  ( 12.1 %)

### Going further

The following results were not part of the original paper, but offer interesting
additional data for interested readers.

#### Improving ASIC synthesis results with retiming

The Makefile in the `koika/examples/rv` directory contains an extra
`nangate-retiming` target, which uses more advanced ABC optimizations, including
register-retiming.  The results should look similar to the following:

    Kôika: ABC: WireLoad = "none"  Gates =   6425 ( 23.4 %)   Cap =  2.2 ff (  1.2 %)   Area =     5503.81 ( 92.8 %)   Delay =   296.87 ps  (  5.4 %)
    BSV: ABC: WireLoad = "none"  Gates =   6505 ( 22.3 %)   Cap =  2.3 ff (  1.1 %)   Area =     5436.77 ( 93.1 %)   Delay =   258.45 ps  (  2.1 %)

#### Synthesizing for FPGA

The file `top_fpga.v` in `koika/examples/rv/_objects/rv32.v/` contains a Verilog
wrapper for our core suitable for placement on an FPGA: it includes a UART
module for external communication, accessed by writing to the special address
`0x40000000` (in the usual `top.v`, writes to that address are mapped to a
Verilog `$fwrite` call).

If you own an FPGA with a 2-port BRAM (we used a Xilinx Artix-7 FPGA AC701), you
can run our design on it.  The specific process depends on your brand: for
Xilinx Series 7 devices, you would install the free edition of Vivado as
explained in https://github.com/timvideos/litex-buildenv/wiki/Xilinx-Vivado,
then synthesize a bitstream using `top_fpga.v` along with the other `.v` files
placed by our compiler in `koika/examples/rv/_objects/rv32.v/`.

### Conclusion

Thanks for evaluating this artifact! We hope that these instructions will be
useful in exploring and evaluating our work.  Feel free to browse the repository
further: if you put new `.v` files in `examples/` or `tests/`, they will be
picked up by our top-level Makefile; they can be compiled by running `make` in
the `koika/` folder.

Happy hacking!
