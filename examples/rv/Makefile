include etc/Makefile.conf

dut := rv32i_core_pipelined
objects_dir := _objects/$(dut).v
opt_cuttlesim := $(dut).opt
opt_verilator := obj_dir/V$(basename $(VERILATOR_TOPLEVEL))
tests_build := tests/_build

all: cuttlesim-tests verilator-tests

core:
	$(MAKE) -C ../.. examples/rv/$(objects_dir)

$(tests_build):
	$(MAKE) -C tests

cuttlesim-tests: core $(tests_build)
	echo "Running RISCV tests:"
	find $(tests_build)/rv32ui/ -name "*.rv32" -exec \
		bash -c "echo 'Test {}'; $(objects_dir)/$(opt_cuttlesim) {} -1; if [ \$$? -eq 0 ]; then echo '[0;32mPassed[0m'; else echo '[0;31mFailed[0m {}'; fi" \;
	time $(objects_dir)/$(opt_cuttlesim) $(tests_build)/integ/primes.rv32 -1

$(objects_dir)/mem.vmh: $(tests_build)/integ/primes.vmh
	cp $< $@

verilator-tests: core $(tests_build) $(objects_dir)/mem.vmh
	$(MAKE) -C $(objects_dir) $(opt_verilator)
	cd $(objects_dir); time $(opt_verilator)

clean:
	rm -rf $(tests_build) ../../_build/default/examples/rv/

.PHONY: all $(tests_build) cuttlesim-tests verilator-tests clean
