.PHONY: all clean

build := _build
elf2hex := elf2hex/elf2hex

integ_sources := $(wildcard integ/*.c)
rv32ui_sources := $(wildcard riscv_tests/rv32ui/*.S)
rv32um_sources := $(wildcard riscv_tests/rv32um/*.S)
integ_objects := $(patsubst %.c,$(build)/%.o,$(integ_sources))
rv32ui_objects := $(patsubst %.S,$(build)/%.o,$(rv32ui_sources))
rv32um_objects := $(patsubst %.S,$(build)/%.o,$(rv32um_sources))

objects := $(integ_objects) $(rv32ui_objects) $(rv32um_objects)
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

$(build) $(build)/integ/ $(build)/riscv_tests/rv32ui/ $(build)/riscv_tests/rv32um/:
	mkdir -p $@

$(elf2hex):
	$(MAKE) -C elf2hex

$(build)/init32.o: init.S | $(build)
	$(cc) -c $< -o $@

$(build)/mmio32.o: mmio.c | $(build)
	$(cc) -c $< -o $@

$(build)/integ/%.o: integ/%.c | $(build)/integ/
	$(cc) -c $< -o $@

$(build)/riscv_tests/rv32ui/%.rv32: riscv_tests/rv32ui/%.S | $(build)/riscv_tests/rv32ui/
	$(cc) -I rv32ui -Tmmio.ld $< -o $@

$(build)/riscv_tests/rv32um/%.rv32: riscv_tests/rv32um/%.S | $(build)/riscv_tests/rv32um/
	$(cc) -I rv32um -Tmmio.ld $< -o $@

$(build)/integ/%.rv32: $(build)/integ/%.o $(build)/init32.o $(build)/mmio32.o mmio.ld
	$(cc) -Tmmio.ld $< $(build)/init32.o $(build)/mmio32.o -o $@

$(build)/%.dump: $(build)/%.rv32
	$(objdump) $< > $@

$(build)/%.vmh: $(build)/%.rv32 $(elf2hex)
	$(elf2hex) $< 0 64K 4 $@

clean:
	rm -rf $(build)

.SUFFIXES:
.SECONDARY:
