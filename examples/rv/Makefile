obj_dir := _objects/rv32i_core_pipelined.v
opt := $(obj_dir)/rv32i_core_pipelined.opt
RISCVCC32=riscv-none-embed-gcc -march=rv32i -mabi=ilp32 -nostartfiles -static -mstrict-align # -nostdlib -nostartfiles # -mcmodel=medany

FULLASMTESTS=$(patsubst fullasmtests/%.S, build/fullasmtests/%32, $(wildcard fullasmtests/*.S))

all: test

core:
	$(MAKE) -C ../.. examples/rv/$(obj_dir)

test: fullasmtests core
	echo "Testing full asm tests:\n"
	find build/fullasmtests/ -name "*32" -exec bash -c "echo 'Test {}'; $(opt) {} 2000000; if [ \$$? -eq 0 ]; then echo '[0;32mPassed[0m'; else echo '[0;31mFailed[0m {}'; fi" \;

fullasmtests: $(FULLASMTESTS)

# fullasmtests targets

build/fullasmtests/%32: fullasmtests/%.S
	@mkdir -p build/fullasmtests
	$(RISCVCC32) -I fullasmtests -Wl,-Tetc/mmio.ld $^ -o $@

clean:
	rm -rf build __pycache__ tools/__pycache__
	rm -f *.dump *.vmh *.x86
	rm -rf ../../_build/default/examples/rv/

.PHONY: all pipetests fullasmtests  clean
