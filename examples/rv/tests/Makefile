.PHONY: all clean dirs

build := _build
elf2hex := elf2hex/elf2hex

asm_rv32i_sources := $(wildcard riscv_tests/rv32ui/*.S) $(wildcard riscv_tests/rv32um/*.S) $(wildcard unit/*.S)
c_rv32i_sources := $(wildcard unit/*.c) $(wildcard integ/*.c)
c_rv32e_sources := $(filter-out $(wildcard integ/rvbench_*),$(c_rv32i_sources))

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
cc32i := $(cc) -march=rv32im -mabi=ilp32 -T$(build)/rv32i/mmio.ld
cc32e := $(cc) -march=rv32e -mabi=ilp32e -T$(build)/rv32e/mmio.ld -DRV32E

all: $(rv32_targets) $(vmh_targets) $(dump_targets);

dirs:
	mkdir -p $(build)
	mkdir -p $(build)/rv32i/ $(build)/rv32i/riscv_tests/rv32ui/ $(build)/rv32i/riscv_tests/rv32um/ $(build)/rv32i/unit/ $(build)/rv32i/integ/
	mkdir -p $(build)/rv32e/ $(build)/rv32e/unit/ $(build)/rv32e/integ/

$(elf2hex):
	$(MAKE) -C elf2hex

$(build)/rv32e/mmio.ld: mmio.ld | dirs
	$(cc) -DRV32E -E -x c $< | grep -v '^#' > $@

$(build)/rv32i/mmio.ld: mmio.ld | dirs
	$(cc) -E -x c $< | grep -v '^#' > $@

$(build)/rv32e/%.rv32: %.S $(build)/rv32e/mmio.ld | dirs
	$(cc32e) -I rv32ui $< -o $@

$(build)/rv32e/%.rv32: %.c init.S init.S mmio.c $(build)/rv32e/mmio.ld | dirs
	$(cc32e) init.S mmio.c $< -o $@

$(build)/rv32i/%.rv32: %.S $(build)/rv32i/mmio.ld | dirs
	$(cc32i) $< -o $@

$(build)/rv32i/%.rv32: %.c init.S mmio.c $(build)/rv32i/mmio.ld | dirs
	$(cc32i) init.S mmio.c $< -o $@

$(build)/%.dump: $(build)/%.rv32
	$(objdump) $< > $@

$(build)/%.vmh: $(build)/%.rv32 $(elf2hex)
	$(elf2hex) $< 0 64K 4 $@

clean:
	rm -rf $(build)

.SUFFIXES:
.SECONDARY:
