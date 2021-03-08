include etc/Makefile.conf

.DEFAULT_GOAL := all
SHELL := bash

export DUT ?= rv32i
objects_dir := _objects/$(DUT).v
tests_build := tests/_build/
tests_build_dut := tests/_build/$(DUT)

cuttlesim := $(objects_dir)/$(basename $(CUTTLESIM_DRIVER)).opt
verilator := $(objects_dir)/obj_dir.opt/V$(basename $(VERILATOR_TOP))
pyverilator := $(objects_dir)/rvcore.pyverilator.py

PYVERILATOR_TOP ?= $(VERILATOR_TOP)
PYVERILATOR_PROBES ?= '*inst*_count' '*cycle_count'
cuttlesim_runner := tests/run.sh "$(cuttlesim)" {} -1
verilator_runner := tests/run.sh "$(verilator)" +VMH={} -1
pyverilator_runner := tests/run.sh "$(pyverilator)" {} -1 --vtop $(PYVERILATOR_TOP) --exit-probes $(PYVERILATOR_PROBES)

DRIVER ?= sv

VERBOSE ?=
verbose := $(if $(VERBOSE),,@)

all: cuttlesim-tests verilator-tests

# The UART module is written in Kôika too, and copied here from the `examples/` folder
uart:
	$(MAKE) -C ../.. examples/_objects/uart.v/
	cp ../../examples/_objects/uart.v/uart.v etc/sv/

core:
	$(MAKE) -C ../.. examples/rv/$(objects_dir)
	$(verbose)cp $(objects_dir)/$(DRIVER)/*.v $(objects_dir)/
	$(verbose)cp $(objects_dir)/Makefile.$(DUT).conf $(objects_dir)/Makefile.platform.conf

$(tests_build_dut): .FORCE
	$(MAKE) -C tests

$(objects_dir)/%: core .FORCE
	$(MAKE) -C $(objects_dir) $*

binaries: $(tests_build_dut);
verilator: $(verilator);
cuttlesim: $(cuttlesim);

.FORCE:

# Unit tests are not run every time, because they are verbose (they are mostly
# useful for debugging, esp. on FPGA)

cuttlesim-tests: binaries cuttlesim
	@echo "-- Running tests with Cuttlesim --"
	find $(tests_build_dut)/ -not -path "*/unit/*" -name "*.rv32" -exec $(cuttlesim_runner) \;

verilator-tests: binaries verilator
	@echo "-- Running tests with Verilator --"
	find $(tests_build_dut)/ -not -path "*/unit/*" -name "*.vmh" -exec $(verilator_runner) \;

pyverilator-tests: binaries core
	@echo "-- Running tests with PyVerilator --"
	find $(tests_build_dut)/integ/ -name "*.vmh" -exec $(pyverilator_runner) \;

nangate45-synthesis: core
	cd $(objects_dir)/nangate45; SCRIPT_DIR=default ./synth.sh

nangate45-retiming: core
	cd $(objects_dir)/nangate45; SCRIPT_DIR=retiming ./synth.sh

clean:
	rm -rf $(tests_build) $(cuttlesim) $(verilator) ../../_build/default/examples/rv/

purge:
	rm -rf _objects

.PHONY: all .FORCE cuttlesim-tests verilator-tests nangate45-synthesis nangate45-retiming clean
