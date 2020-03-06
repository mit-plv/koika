.PHONY: all clean dirs

build := _build
elf2hex := elf2hex/elf2hex

asm_sources := $(wildcard riscv_tests/rv32ui/*.S) $(wildcard riscv_tests/rv32um/*.S) $(wildcard unit/*.S)
c_sources := $(wildcard unit/*.c) $(wildcard integ/*.c)
asm_objects := $(patsubst %.S,$(build)/%.o,$(asm_sources))
c_objects := $(patsubst %.c,$(build)/%.o,$(c_sources))

objects := $(c_objects) $(asm_objects)
rv32_targets := $(patsubst %.o,%.rv32,$(objects))
vmh_targets := $(patsubst %.o,%.vmh,$(objects))
dump_targets := $(patsubst %.o,%.dump,$(objects))

RISCVCC32 ?= riscv-none-embed-gcc
RISCVCC32_ARGS := -g -march=rv32im -mabi=ilp32 -mstrict-align -nostartfiles -static
RISCVOBJDUMP32 ?= riscv-none-embed-objdump
RISCVOBJDUMP32_ARGS := --disassemble --source --full-contents

cc := $(RISCVCC32) $(RISCVCC32_ARGS)
objdump := $(RISCVOBJDUMP32) $(RISCVOBJDUMP32_ARGS)

all: $(rv32_targets) $(vmh_targets) $(dump_targets);

dirs:
	mkdir -p $(build) $(build)/riscv_tests/rv32ui/ $(build)/riscv_tests/rv32um/ $(build)/unit/ $(build)/integ/

$(elf2hex):
	$(MAKE) -C elf2hex

$(build)/init32.o: init.S | dirs
	$(cc) -c $< -o $@

$(build)/mmio32.o: mmio.c | dirs
	$(cc) -c $< -o $@

$(build)/%.o: %.c | dirs
	$(cc) -c $< -o $@

arch = $(if $(findstring rv32ui,$1),rv32ui,rv32um)

$(build)/%.rv32: %.S | dirs
	$(cc) -I $(arch $<) -Tmmio.ld $< -o $@

$(build)/%.rv32: $(build)/%.o $(build)/init32.o $(build)/mmio32.o mmio.ld
	$(cc) -Tmmio.ld $< $(build)/init32.o $(build)/mmio32.o -o $@

$(build)/%.dump: $(build)/%.rv32
	$(objdump) $< > $@

$(build)/%.vmh: $(build)/%.rv32 $(elf2hex)
	$(elf2hex) $< 0 64K 4 $@

clean:
	rm -rf $(build)

.SUFFIXES:
.SECONDARY:
