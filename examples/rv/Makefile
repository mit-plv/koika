include etc/Makefile.conf

dut := rv32i_core_pipelined
objects_dir := _objects/$(dut).v
tests_build := tests/_build

cuttlesim := $(objects_dir)/$(basename $(CUTTLESIM_DRIVER)).opt
verilator := $(objects_dir)/obj_dir/V$(basename $(VERILATOR_TOPLEVEL))
pyverilator := $(objects_dir)/rvcore.pyverilator.py

PYVERILATOR_TOP ?= top.v
PYVERILATOR_PROBES ?= '*inst*_count' '*cycle_count'
cuttlesim_runner := tests/run.sh "$(cuttlesim)" {}
verilator_runner := tests/run.sh "$(verilator)" {}
pyverilator_runner := tests/run.sh "$(pyverilator)" {} --vtop $(PYVERILATOR_TOP) --exit-probes $(PYVERILATOR_PROBES)

DRIVER ?= bsv

all: cuttlesim-tests verilator-tests

core:
	$(MAKE) -C ../.. examples/rv/$(objects_dir)
	cp $(objects_dir)/$(DRIVER)/*.v $(objects_dir)/

$(tests_build): .FORCE
	$(MAKE) -C tests

$(objects_dir)/%: core .FORCE
	$(MAKE) -C $(objects_dir) $*

binaries: $(tests_build);
verilator: $(verilator);
cuttlesim: $(cuttlesim);

.FORCE:

cuttlesim-tests: binaries cuttlesim
	@echo "-- Running tests with Cuttlesim --"
	find $(tests_build)/rv32ui -name "*.rv32" -exec $(cuttlesim_runner) \;
	find $(tests_build)/integ -name "*.rv32" -exec $(cuttlesim_runner) \;

verilator-tests: binaries verilator
	@echo "-- Running tests with Verilator --"
	find $(tests_build)/rv32ui -name "*.vmh" -exec $(verilator_runner) \;
	find $(tests_build)/integ -name "*.vmh" -exec $(verilator_runner) \;

pyverilator-tests: binaries
	@echo "-- Running tests with PyVerilator --"
	find $(tests_build)/rv32ui -name "*.vmh" -exec $(pyverilator_runner) \;
	find $(tests_build)/integ -name "*.vmh" -exec $(pyverilator_runner) \;

nangate45-synthesis: core
	cd $(objects_dir)/nangate45; ./synth.sh

clean:
	rm -rf $(tests_build) $(cuttlesim) $(verilator) ../../_build/default/examples/rv/

purge:
	rm -rf _objects

.PHONY: all .FORCE cuttlesim-tests verilator-tests clean
