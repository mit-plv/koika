==============
 ``RVCore.v``
==============

This is our Kôika implementation of a pipelined CPU core implementing RV32I.

Dependencies
============

- The `usual dependencies <../../README.rst>`_ to run Kôika.
- A cross-compiling toolchain: `riscv-none-embed-gcc <https://github.com/xpack-dev-tools/riscv-none-embed-gcc-xpack/releases/>`_.
- For RTL simulation: `Verilator <https://www.veripool.org/wiki/verilator>`_ (or your own tools)
- For synthesis: `YoSys <http://www.clifford.at/yosys/>`_, `NextPNR <https://github.com/YosysHQ/nextpnr>`_, and `IceStorm <https://github.com/cliffordwolf/icestorm>`_ (or your own tools; see below for more details)

Compiling and running
=====================

- To build the core: ``make core``
- To run the tests in CuttleSim (our simulator): ``make cuttlesim-tests``
- To run the tests in Verilator: ``make verilator-tests``

Both test targets run unit tests followed by a few integration tests.

Additional targets (for debugging, tracing, profiling, etc.) are provided by the auto-generated Makefile.  After ``make core``, go to ``_objects/rv32.v/`` and run ``make help`` for more information.

Synthesis
=========

We test regularly on a `ULX3S <https://radiona.org/ulx3s/>`_ board, and occasionally on a Xilinx Artix-7 (AC701). Follow the instructions in the main makefile to build an example.

The `TinyFPGA BX <https://tinyfpga.com/bx/guide.html>`_ is a reasonable target too, though it is too small to fit the RV32I core comfortably.  The RV32E core fits as long as you use the UART interface (``make ICE40_TOP=top_ice40_uart.v top_ice40_uart.bit``).  The alternative would be to connect through USB, but it's hard to fit both a USB controller and the core on the device.
