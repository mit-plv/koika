==============
 ``RVCore.v``
==============

This is our Kôika implementation of a pipelined CPU core implementing RV32I.

Dependencies
============

- The `usual dependencies <../../README.rst>`_ to run Kôika.
- A cross-compiling toolchain: `riscv-none-embed-gcc <https://github.com/xpack-dev-tools/riscv-none-embed-gcc-xpack/releases/>`.

Compiling and running
=====================

- To build the core: ``make core``
- To run the tests in our own simulator: ``make cuttlesim-tests``
- To run the tests in Verilator: ``make verilator-tests``

Both test targets run simple tests and then run a simple program rendering the Mandelbrot fractal.

Additional targets (for debugging, tracing, profiling, etc.) are provided by the auto-generated Makefile.  After ``make core``, go to ``_objects/rv32i_core_pipelined.v/`` and run ``make help`` for more information.
