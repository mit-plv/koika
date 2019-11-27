.PHONY: all clean

SRCDIR=src
BUILDDIR=build

bmarks = \
	median_main \
	qsort_main

SOURCES=$(notdir $(foreach bench,$(bmarks),$(wildcard $(SRCDIR)/$(bench).c)))
# SOURCES=$(notdir $(wildcard $(SRCDIR)/*.c))
TESTS=$(basename $(SOURCES))
ELF=$(addprefix build/,$(TESTS))
ELF32=$(addsuffix 32,$(ELF))

RISCVCC32=riscv-none-embed-gcc -march=rv32i -mabi=ilp32 -mstrict-align -nostartfiles -static # -nostdlib -nostartfiles # -mcmodel=medany
#RISCVCC32=riscv64-unknown-linux-gnu-gcc  -march=rv32i -mabi=ilp32 -static -nostdlib -nostartfiles -mcmodel=medany



all: $(ELF32)

ELF2HEX := ../elf2hex

$(ELF2HEX)/elf2hex:
	$(MAKE) -C $(ELF2HEX)

init32.o: init.S
	$(RISCVCC32) -c init.S -o init32.o

mmio32.o: mmio.c
	$(RISCVCC32) -c mmio.c -o mmio32.o


$(BUILDDIR)/%32: $(SRCDIR)/%.c $(ELF2HEX)/elf2hex init32.o mmio32.o mmio.ld
	mkdir -p $(BUILDDIR)
	$(RISCVCC32) -c $(SRCDIR)/$*.c -o intermediate32.o
	$(RISCVCC32) -o $(BUILDDIR)/$*32 -Tmmio.ld intermediate32.o init32.o mmio32.o
	$(ELF2HEX)/elf2hex $(BUILDDIR)/$*32 0 64K 4 $(BUILDDIR)/$*.vmh
	rm intermediate32.o

clean:
	rm -f intermediate32.o init32.o mmio32.o
	rm -rf build
