OUTPUT_ARCH("riscv")
ENTRY(_start)

_ADDRESS_WIDTH = 16; /* 256kiB of memory, 64kiB of stack */
_MEMSIZE = (1 << _ADDRESS_WIDTH) * 4;
_MIN_STACK_SIZE = (1 << _ADDRESS_WIDTH);

_ORIGIN1 = 0x00100000;
_ORIGIN2 = 0x00200000;
_ORIGIN3 = 0x00300000;

_fstack0 = _MEMSIZE - 16;
_fstack1 = _ORIGIN1 + (_MEMSIZE - 16);
_fstack2 = _ORIGIN2 + (_MEMSIZE - 16);

_glbl0 = _MEMSIZE - 12;


MEMORY {
  mem0_init (rx) : ORIGIN = 0x0, LENGTH = 0x1000
  mem0_bootloader (rx) : ORIGIN = 0x1000, LENGTH = 0x2000
  mem0_start (rx) : ORIGIN = 0x2000, LENGTH = _MEMSIZE - _MIN_STACK_SIZE - 0x2000

  mem1 (rx) : ORIGIN = _ORIGIN1, LENGTH = _MEMSIZE - _MIN_STACK_SIZE

  mem2 (rx) : ORIGIN = _ORIGIN2, LENGTH = _MEMSIZE - _MIN_STACK_SIZE

  mem3 (rx) : ORIGIN = _ORIGIN3, LENGTH = _MEMSIZE - _MIN_STACK_SIZE
}

SECTIONS
{

  .text.enclave0.init : { *(.text.enclave0.init) } > mem0_init
  .text.enclave0.bootloader : { *(.text.enclave0.bootloader) } > mem0_bootloader
  .text.enclave0.main : { *(.text.enclave0.main) } > mem0_start
  .text.enclave0 : { enclave0.o(.text .text.*) } > mem0_start
  .text.mmio0 : { multicore_mmio0.o(.text .text.*) } > mem0_start
  .enclave0 : { enclave0.o } > mem0_start
  .mmio0 : { multicore_mmio0.o } > mem0_start

  .text.init1 : { *(.text.init1) } > mem1
  .text.core1 : { null.o(.text .text.*) } > mem1
  .text.mmio1 : { multicore_mmio1.o(.text .text.*) } > mem1
  .core1 : { null.o } > mem1
  .mmio1 : { multicore_mmio1.o } > mem1

  .text.enclave2.bootloader2 : { *(.text.enclave2.bootloader) } > mem2
  .text.enclave2 : { enclave2.o(.text .text.*) } > mem2
  .text.mmio2 : { multicore_mmio2.o(.text .text.*) } > mem2
  .enclave2 : { enclave2.o } > mem2
  .mmio2 : { multicore_mmio2.o } > mem2

   .text : { *(.text .text.*) } > mem3
  .data : { *(.data) } > mem3
  .bss : { *(.bss) } > mem3

  _end = .;
}
