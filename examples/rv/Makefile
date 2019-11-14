
RISCVCC32=riscv-none-embed-gcc -march=rv32i -mabi=ilp32 -nostartfiles -static -mstrict-align # -nostdlib -nostartfiles # -mcmodel=medany

FULLASMTESTS=$(patsubst fullasmtests/%.S, build/fullasmtests/%32, $(wildcard fullasmtests/*.S))


all: core fullasmtests

core:
	$(MAKE) -C ../.. examples/rv/RVCore.v.objects/

fullasmtests: $(FULLASMTESTS)

# fullasmtests targets

build/fullasmtests/%32: fullasmtests/%.S
	@mkdir -p build/fullasmtests
	$(RISCVCC32) -I fullasmtests -Wl,-Tmmio.ld $^ -o $@

clean:
	rm -rf build __pycache__ tools/__pycache__
	rm -f *.dump *.vmh *.x86
	rm -rf ../../_build/default/examples/rv/

.PHONY: all pipetests fullasmtests  clean
