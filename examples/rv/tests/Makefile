.PHONY: all clean

build := _build
elf2hex := elf2hex/elf2hex

integ_sources := $(wildcard integ/*.c)
rv32ui_sources := $(wildcard rv32ui/*.S)
integ_objects := $(patsubst %.c,$(build)/%.o,$(integ_sources))
rv32ui_objects := $(patsubst %.S,$(build)/%.o,$(rv32ui_sources))

rv32_targets := $(patsubst %.o,%.rv32,$(integ_objects) $(rv32ui_objects))
vmh_targets := $(patsubst %.o,%.vmh,$(integ_objects) $(rv32ui_objects))

RISCVCC32 ?= riscv-none-embed-gcc
RISCVCC32_ARGS := -march=rv32im -mabi=ilp32 -mstrict-align -nostartfiles -static

cc := $(RISCVCC32) $(RISCVCC32_ARGS)

all: $(rv32_targets) $(vmh_targets);

$(build) $(build)/integ/ $(build)/rv32ui/:
	mkdir -p $@

$(elf2hex):
	$(MAKE) -C elf2hex

$(build)/init32.o: init.S | $(build)
	$(cc) -c $< -o $@

$(build)/mmio32.o: mmio.c | $(build)
	$(cc) -c $< -o $@

$(build)/integ/%.o: integ/%.c | $(build)/integ/
	$(cc) -c $< -o $@

$(build)/rv32ui/%.rv32: rv32ui/%.S | $(build)/rv32ui/
	$(cc) -I rv32ui -Tmmio.ld $< -o $@

$(build)/rv32um/%.rv32: rv32um/%.S | $(build)/rv32um/
	$(cc) -I rv32um -Tmmio.ld $< -o $@

$(build)/integ/%.rv32: $(build)/integ/%.o $(build)/init32.o $(build)/mmio32.o mmio.ld
	$(cc) -Tmmio.ld $< $(build)/init32.o $(build)/mmio32.o -o $@

$(build)/%.vmh: $(build)/%.rv32 $(elf2hex)
	$(elf2hex) $< 0 64K 4 $@

clean:
	rm -rf $(build)

.SUFFIXES:
.SECONDARY:
