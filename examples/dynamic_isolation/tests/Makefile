.PHONY: all clean dirs

build := _build
elf2hex := elf2hex/elf2hex

asm_rv32i_sources := $(wildcard riscv_tests/rv32ui/*.S) $(wildcard riscv_tests/rv32um/*.S) $(wildcard unit/*.S)
c_rv32i_sources := $(wildcard unit/*.c) $(wildcard integ/*.c)
c_rv32e_sources := $(filter-out $(wildcard integ/rvbench_*),$(c_rv32i_sources))

#asm_multicore_sources := $(wildcard riscv_tests/rv32ui/*.S) $(wildcard riscv_tests/rv32um/*.S) $(wildcard unit/*.S)
c_multicore_sources := $(wildcard multicore/*.c) 

asm_rv32i_stems := $(patsubst %.S,$(build)/rv32i/%,$(asm_rv32i_sources))
c_rv32i_stems := $(patsubst %.c,$(build)/rv32i/%,$(c_rv32i_sources))
c_rv32e_stems := $(patsubst %.c,$(build)/rv32e/%,$(c_rv32e_sources))

asm_multicore_stems := $(patsubst %.S,$(build)/multicore/%,$(asm_multicore_sources))
c_multicore_stems := $(patsubst %.c,$(build)/multicore/%,$(c_multicore_sources))

stems := $(c_rv32i_stems) $(c_rv32e_stems) $(asm_rv32i_stems) # $(c_multicore_stems) $(asm_multicore_stems)
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
#cc32m = $(cc) -T$(build)/multicore/multicore_link.ld -mabi=ilp32

multicore_targets := $(build)/multicore/basic.rv32

all: $(rv32_targets) $(vmh_targets) $(dump_targets) $(multicore_targets);


dirpatterns := %/rv32i/ %/rv32i/riscv_tests/rv32ui/ %/rv32i/riscv_tests/rv32um/ %/rv32i/unit/ %/rv32i/integ/ %/rv32e/ %/rv32e/unit/ %/rv32e/integ/ 

multicore_dirpatterns := %/multicore/ %/multicore/riscv_tests/rv32ui/ %/multicore/riscv_tests/rv32um/ %/multicore/unit/ %/multicore/integ/ %/multicore/multicore/

dirs := $(patsubst \%%,$(build)%,$(dirpatterns))

multicore_dirs := $(patsubst \%%,$(build)%,$(multicore_dirpatterns))

$(dirpatterns):
	mkdir -p $(dirs)

$(multicore_dirpatterns):
	mkdir -p $(multicore_dirs)

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

$(build)/multicore/multicore_init.o: multicore_init.S | $(multicore_dirs)
	$(cc) -march=rv32i -c $< -o $@

#$(build)/multicore/mmio32.o: multicore_mmio.c | $(build)
#	$(cc) -c $< -o $@

$(build)/multicore/multicore_link.ld: multicore_link.ld | $(multicore_dirs)
	$(cc) -E -x c $< | grep -v '^#' > $@

#$(build)/multicore/%.rv32: %.S $(build)/multicore/multicore_link.ld | $(multicore_dirs)
#	$(cc32m) -march=$(call iarch,$<) $< -o $@

$(build)/multicore/%.o: %.c | $(multicore_dirs)
	$(cc) -march=rv32i -c $< -o $@

$(build)/multicore/basic_core0.o: basic_core0.c | $(multicore_dirs)
	$(cc) -march=rv32i -c $< -o $@

$(build)/multicore/basic_core1.o: basic_core1.c | $(multicore_dirs)
	$(cc) -march=rv32i -c $< -o $@

$(build)/multicore/multicore_mmio0.o: multicore_mmio0.c | $(multicore_dirs)
	$(cc) -march=rv32i -c $< -o $@

$(build)/multicore/multicore_mmio1.o: multicore_mmio1.c | $(multicore_dirs)
	$(cc) -march=rv32i -c $< -o $@


#$(build)/multicore/%.rv32: %.c multicore_init.S multicore_mmio.c $(build)/multicore/multicore_link.ld | $(multicore_dirs)
#	$(cc32m) -march=$(call iarch,$<) multicore_init.S multicore_mmio.c $< -o $@

$(build)/multicore/basic.rv32: $(build)/multicore/basic_core0.o $(build)/multicore/basic_core1.o $(build)/multicore/multicore_init.o $(build)/multicore/multicore_mmio0.o $(build)/multicore/multicore_mmio1.o $(build)/multicore/multicore_link.ld | $(multicore_dirs)
	cd $(build)/multicore;
	$(cc) -Tmulticore_link.ld -mabi=ilp32 -march=rv32i multicore_init.o multicore_mmio0.o multicore_mmio1.o basic_core0.o basic_core1.o -o basic.rv32

#$(build)/multicore/multicore/basic.rv32: multicore/basic_core0.c multicore/basic_core1.c multicore_init.S multicore_mmio.c $(build)/multicore/multicore_link.ld 
#	$(cc32m) -march=$(call iarch,$<) multicore_init.S multicore_mmio.c multicore/basic_core0.c multicore/basic_core1.c -o $@


$(build)/%.dump: $(build)/%.rv32
	$(objdump) $< > $@

$(build)/%.dump: $(build)/%.o
	$(objdump) $< > $@

$(build)/%.vmh: $(build)/%.rv32 $(elf2hex)
	$(elf2hex) $< 0 64K 4 $@

clean:
	rm -rf $(build)

.SUFFIXES:
.SECONDARY:
