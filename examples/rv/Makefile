include etc/Makefile.conf

dut := rv32i_core_pipelined
objects_dir := _objects/$(dut).v
opt_cuttlesim := $(basename $(CUTTLESIM_DRIVER)).opt
opt_verilator := obj_dir/V$(basename $(VERILATOR_TOPLEVEL))
tests_build := tests/_build

verilator := $(objects_dir)/$(opt_verilator)
cuttlesim := $(objects_dir)/$(opt_cuttlesim)
cuttlesim_runner := tests/run.sh "$(cuttlesim)"
verilator_runner := tests/run.sh "$(verilator)"

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
	find $(tests_build)/rv32ui -name "*.rv32" -exec $(cuttlesim_runner) {} \;
	find $(tests_build)/integ -name "*.rv32" -exec $(cuttlesim_runner) {} \;

verilator-tests: binaries verilator
	@echo "-- Running tests with Verilator --"
	find $(tests_build)/rv32ui -name "*.vmh" -exec $(verilator_runner) {} \;
	find $(tests_build)/integ -name "*.vmh" -exec $(verilator_runner) {} \;

nangate45-synthesis: binaries
	@echo "-- Synthesisizing against Nangate Open Cell Library (45nm) --"
	$(MAKE) -C $(objects_dir)/etc/nangate45

clean:
	rm -rf $(tests_build) $(cuttlesim) $(verilator) ../../_build/default/examples/rv/

.PHONY: all .FORCE cuttlesim-tests verilator-tests clean
