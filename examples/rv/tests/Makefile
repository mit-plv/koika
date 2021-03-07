.PHONY: all clean dirs

build := _build
elf2hex := elf2hex/elf2hex

asm_rv32i_sources := $(wildcard riscv_tests/rv32ui/*.S) $(wildcard riscv_tests/rv32um/*.S) $(wildcard unit/*.S)
c_rv32i_sources := $(wildcard unit/*.c) $(wildcard integ/*.c)
c_rv32e_sources := $(filter-out integ/img.c,$(filter-out $(wildcard integ/rvbench_*),$(c_rv32i_sources)))

asm_rv32i_stems := $(patsubst %.S,$(build)/rv32i/%,$(asm_rv32i_sources))
c_rv32i_stems := $(patsubst %.c,$(build)/rv32i/%,$(c_rv32i_sources))
c_rv32e_stems := $(patsubst %.c,$(build)/rv32e/%,$(c_rv32e_sources))

stems := $(c_rv32i_stems) $(c_rv32e_stems) $(asm_rv32i_stems)
rv32_targets := $(stems:=.rv32)
vmh_targets := $(stems:=.vmh)
dump_targets := $(stems:=.dump)

RISCVCC32 ?= riscv-none-embed-gcc
RISCVCC32_ARGS := -g -mstrict-align -nostartfiles -static
RISCVOBJDUMP32 ?= riscv-none-embed-objdump
RISCVOBJDUMP32_ARGS := --disassemble --source --full-contents

cc := $(RISCVCC32) $(RISCVCC32_ARGS)
objdump := $(RISCVOBJDUMP32) $(RISCVOBJDUMP32_ARGS)
iarch = $(if $(findstring riscv_tests/rv32ui,$1),rv32i,rv32im)
cc32i = $(cc) -T$(build)/rv32i/link.ld -mabi=ilp32
cc32e = $(cc) -T$(build)/rv32e/link.ld -DRV32E -mabi=ilp32e -march=rv32e

all: $(rv32_targets) $(vmh_targets) $(dump_targets);

dirpatterns := %/rv32i/ %/rv32i/riscv_tests/rv32ui/ %/rv32i/riscv_tests/rv32um/ %/rv32i/unit/ %/rv32i/integ/ %/rv32e/ %/rv32e/unit/ %/rv32e/integ/
dirs := $(patsubst \%%,$(build)%,$(dirpatterns))

$(dirpatterns):
	mkdir -p $(dirs)

$(elf2hex):
	$(MAKE) -C elf2hex

$(build)/rv32e/link.ld: link.ld | $(dirs)
	$(cc) -DRV32E -E -x c $< | grep -v '^#' > $@

$(build)/rv32i/link.ld: link.ld | $(dirs)
	$(cc) -E -x c $< | grep -v '^#' > $@

$(build)/rv32e/%.rv32: %.S $(build)/rv32e/link.ld | $(dirs)
	$(cc32e) -I rv32ui $< -o $@

$(build)/rv32e/%.rv32: %.c init.S init.S mmio.c $(build)/rv32e/link.ld | $(dirs)
	$(cc32e) init.S mmio.c $< -o $@

$(build)/rv32i/%.rv32: %.S $(build)/rv32i/link.ld | $(dirs)
	$(cc32i) -march=$(call iarch,$<) $< -o $@

$(build)/rv32i/%.rv32: %.c init.S mmio.c $(build)/rv32i/link.ld | $(dirs)
	$(cc32i) -march=$(call iarch,$<) init.S mmio.c $< -o $@

$(build)/%.dump: $(build)/%.rv32
	$(objdump) $< > $@

$(build)/%.vmh: $(build)/%.rv32 $(elf2hex)
	$(elf2hex) $< 0 64K 4 $@

clean:
	rm -rf $(build)

.SUFFIXES:
.SECONDARY:
