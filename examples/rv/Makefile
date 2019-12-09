include etc/Makefile.conf

dut := rv32i_core_pipelined
build_dir := _objects/$(dut).v
opt_cuttlesim := $(dut).opt
opt_verilator := obj_dir.opt/V$(basename $(VERILATOR_TOPLEVEL))
RISCVCC32=riscv-none-embed-gcc -march=rv32i -mabi=ilp32 -nostartfiles -static -mstrict-align # -nostdlib -nostartfiles # -mcmodel=medany

FULLASMTESTS=$(patsubst fullasmtests/%.S, build/fullasmtests/%32, $(wildcard fullasmtests/*.S))

all: test

core:
	$(MAKE) -C ../.. examples/rv/$(build_dir)

test/build: $(wildcard test/*.*)
	$(MAKE) -C test

cuttlesim-tests: fullasmtests test/build core
	echo "Testing full asm tests:\n"
	find build/fullasmtests/ -name "*32" -exec bash -c "echo 'Test {}'; $(build_dir)/$(opt_cuttlesim) {} -1; if [ \$$? -eq 0 ]; then echo '[0;32mPassed[0m'; else echo '[0;31mFailed[0m {}'; fi" \;
	time $(build_dir)/$(opt_cuttlesim) test/build/primes32 -1

verilator-tests: test/build core
	cp test/build/primes.vmh $(build_dir)/mem.vmh
	$(MAKE) -C $(build_dir) $(opt_verilator)
	cd $(build_dir); time $(opt_verilator)

test: cuttlesim-tests verilator-tests

fullasmtests: $(FULLASMTESTS);

# fullasmtests targets

build/fullasmtests/%32: fullasmtests/%.S
	@mkdir -p build/fullasmtests
	$(RISCVCC32) -I fullasmtests -Wl,-Tetc/mmio.ld $^ -o $@

clean:
	rm -rf build __pycache__ tools/__pycache__
	rm -f *.dump *.vmh *.x86
	rm -rf ../../_build/default/examples/rv/

.PHONY: all fullasmtests cuttlesim-tests verilator-tests clean
