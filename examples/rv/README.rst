==============
 ``RVCore.v``
==============

This is our Kôika implementation of a pipelined CPU core implementing RV32I.

Dependencies
============

- The `usual dependencies <../../README.rst>`_ to run Kôika.
- A cross-compiling toolchain: `riscv-none-embed-gcc <https://github.com/xpack-dev-tools/riscv-none-embed-gcc-xpack/releases/>`_.
- For RTL simulation: `Verilator <https://www.veripool.org/wiki/verilator>`_ (or your own tools)
- For synthesis: `YoSys <http://www.clifford.at/yosys/>`_ (or your own tools)

Compiling and running
=====================

- To build the core: ``make core``
- To run the tests in CuttleSim (our simulator): ``make cuttlesim-tests``
- To run the tests in Verilator: ``make verilator-tests``

Both test targets run unit tests followed by a few integration tests.

Additional targets (for debugging, tracing, profiling, etc.) are provided by the auto-generated Makefile.  After ``make core``, go to ``_objects/rv32.v/`` and run ``make help`` for more information.
