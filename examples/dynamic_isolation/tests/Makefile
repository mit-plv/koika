.PHONY: all clean dirs

build := _build
elf2hex := elf2hex/elf2hex

asm_rv32i_sources := $(wildcard riscv_tests/rv32ui/*.S) $(wildcard riscv_tests/rv32um/*.S) $(wildcard unit/*.S)
c_rv32i_sources := $(wildcard unit/*.c) $(wildcard integ/*.c)


asm_rv32i_stems := $(patsubst %.S,$(build)/rv32i/%,$(asm_rv32i_sources))
c_rv32i_stems := $(patsubst %.c,$(build)/rv32i/%,$(c_rv32i_sources))

asm_multicore_sources := $(wildcard password_manager/*.S)
asm_multicore_stems := $(patsubst %.S,$(build)/multicore/%,$(asm_multicore_sources))

c_multicore_sources := $(wildcard password_manager/*.c)
c_multicore_stems := $(patsubst %.c,$(build)/multicore/%,$(c_multicore_sources))

stems := $(c_rv32i_stems) $(asm_rv32i_stems) # $(c_multicore_stems) $(asm_multicore_stems)
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
cc32i_c = $(cc) -T$(build)/rv32i/singlecore_link_c.ld -mabi=ilp32
cc32i_rv32 = $(cc) -T$(build)/rv32i/singlecore_link_rv32.ld -mabi=ilp32
#cc32e = $(cc) -T$(build)/rv32e/link.ld -DRV32E -mabi=ilp32e -march=rv32e
#cc32m = $(cc) -T$(build)/multicore/multicore_link.ld -mabi=ilp32

multicore_targets := $(build)/multicore/basic.rv32 $(build)/multicore/password_manager/pwd_manager.rv32
all: $(rv32_targets) $(vmh_targets) $(dump_targets) $(multicore_targets);


dirpatterns := %/rv32i/ %/rv32i/riscv_tests/rv32ui/ %/rv32i/riscv_tests/rv32um/ %/rv32i/unit/ %/rv32i/integ/ %/rv32e/ %/rv32e/unit/ %/rv32e/integ/ 

multicore_dirpatterns := %/multicore/ %/multicore/riscv_tests/rv32ui/ %/multicore/riscv_tests/rv32um/ %/multicore/unit/ %/multicore/integ/ %/multicore/password_manager/

dirs := $(patsubst \%%,$(build)%,$(dirpatterns))

multicore_dirs := $(patsubst \%%,$(build)%,$(multicore_dirpatterns))

$(dirpatterns):
	mkdir -p $(dirs)

$(multicore_dirpatterns):
	mkdir -p $(multicore_dirs)

$(elf2hex):
	$(MAKE) -C elf2hex

$(build)/rv32i/singlecore_init.o: singlecore_init.S | $(dirs)
	$(cc) -march=rv32i -c $< -o $@
$(build)/rv32i/singlecore_init_rv32.o: singlecore_init_rv32.S | $(dirs)
	$(cc) -march=rv32i -c $< -o $@


$(build)/rv32i/singlecore_link_%.ld: singlecore_link_%.ld | $(dirs)
	$(cc) -E -x c $< | grep -v '^#' > $@

$(build)/rv32i/singlecore_mmio%.o: singlecore_mmio%.c | $(dirs)
	$(cc) -march=rv32i -c $< -o $@
$(build)/rv32i/dummy_core1.o: dummy_core1.c | $(dirs)
	$(cc) -march=rv32i -c $< -o $@


$(build)/rv32i/%.rv32: %.S $(build)/rv32i/singlecore_init.o $(build)/rv32i/singlecore_mmio0.o $(build)/rv32i/singlecore_mmio1.o $(build)/rv32i/dummy_core1.o $(build)/rv32i/singlecore_link_rv32.ld | $(dirs)
	$(cc32i_rv32) -L_build/rv32i -march=$(call iarch,$<) singlecore_init_rv32.S $< -o $@

$(build)/rv32i/%.rv32: %.c $(build)/rv32i/singlecore_init.o $(build)/rv32i/singlecore_mmio0.o $(build)/rv32i/singlecore_mmio1.o $(build)/rv32i/dummy_core1.o $(build)/rv32i/singlecore_link_c.ld | $(dirs)
	$(cc32i_c) -L_build/rv32i -march=$(call iarch,$<) singlecore_init.S singlecore_mmio0.c $< -o $@

$(build)/multicore/multicore_init.o: multicore_init.S | $(multicore_dirs)
	$(cc) -march=rv32i -c $< -o $@


$(build)/multicore/multicore_link.ld: multicore_link.ld | $(multicore_dirs)
	$(cc) -E -x c $< | grep -v '^#' > $@

$(build)/multicore/%.o: %.c | $(multicore_dirs)
	$(cc) -march=rv32i -c $< -o $@

$(build)/multicore/basic_core0.o: basic_core0.c | $(multicore_dirs)
	$(cc) -march=rv32i -c $< -o $@

$(build)/multicore/basic_core1.o: basic_core1.c | $(multicore_dirs)
	$(cc) -march=rv32i -c $< -o $@

$(build)/multicore/multicore_mmio%.o: multicore_mmio%.c | $(multicore_dirs)
	$(cc) -march=rv32i -c $< -o $@


$(build)/multicore/basic.rv32: $(build)/multicore/basic_core0.o $(build)/multicore/basic_core1.o $(build)/multicore/multicore_init.o $(build)/multicore/multicore_mmio0.o $(build)/multicore/multicore_mmio1.o $(build)/multicore/multicore_link.ld | $(multicore_dirs)
	cd $(build)/multicore; $(cc) -Tmulticore_link.ld -mabi=ilp32 -march=rv32i multicore_init.o multicore_mmio0.o multicore_mmio1.o basic_core0.o basic_core1.o -o basic.rv32

#
# TODO: generalize
pwd_mngr_dir := $(build)/multicore/password_manager

$(pwd_mngr_dir)/link.ld: password_manager/link.ld | $(multicore_dirs)
	$(cc) -E -x c $< | grep -v '^#' > $@

$(pwd_mngr_dir)/multicore_mmio%.o: multicore_mmio%.c | $(multicore_dirs)
	$(cc) -march=rv32i -c $< -o $@

$(pwd_mngr_dir)/%.o: password_manager/%.c | $(multicore_dirs)
	$(cc) -march=rv32i -c $< -o $@

$(pwd_mngr_dir)/%.o: password_manager/%.S | $(multicore_dirs)
	$(cc) -march=rv32i -c $< -o $@

$(pwd_mngr_dir)/pwd_manager.rv32: $(pwd_mngr_dir)/init_enclave0.o $(pwd_mngr_dir)/init_enclave1.o $(pwd_mngr_dir)/enclave0.o $(pwd_mngr_dir)/null.o $(pwd_mngr_dir)/null.o $(pwd_mngr_dir)/enclave2_bootloader.o $(pwd_mngr_dir)/enclave2.o $(pwd_mngr_dir)/multicore_mmio0.o $(pwd_mngr_dir)/multicore_mmio1.o $(pwd_mngr_dir)/multicore_mmio2.o $(pwd_mngr_dir)/link.ld | $(multicore_dirs)
	cd $(build)/multicore/password_manager; $(cc) -Tlink.ld -mabi=ilp32 -march=rv32i init_enclave0.o enclave0.o init_enclave1.o null.o enclave2_bootloader.o enclave2.o multicore_mmio0.o multicore_mmio1.o multicore_mmio2.o -o pwd_manager.rv32


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
