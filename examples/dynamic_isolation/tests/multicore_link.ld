OUTPUT_ARCH("riscv")
ENTRY(_start0)

_ADDRESS_WIDTH = 16; /* 256kiB of memory, 64kiB of stack */
_MEMSIZE = (1 << _ADDRESS_WIDTH) * 4;
_MIN_STACK_SIZE = (1 << _ADDRESS_WIDTH);

_ORIGIN1 = 0x00100000;
_fstack0 = _MEMSIZE - 4;
_fstack1 = _ORIGIN1 + (_MEMSIZE - 4);

_ORIGIN2 = 0x00200000;

MEMORY {
  mem0 (rx) : ORIGIN = 0x0, LENGTH = _MEMSIZE - _MIN_STACK_SIZE

  mem1 (rx) : ORIGIN = _ORIGIN1, LENGTH = _MEMSIZE - _MIN_STACK_SIZE

  mem2 (rx) : ORIGIN = _ORIGIN2, LENGTH = _MEMSIZE - _MIN_STACK_SIZE
}

SECTIONS
{

  .text.init0 : { *(.text.init0) } > mem0
  .text.core0 : { basic_core0.o(.text .text.*) } > mem0
  .text.mmio0 : { multicore_mmio0.o(.text .text.*) } > mem0
  .core0 : { basic_core0.o } > mem0
  .mmio0 : { multicore_mmio0.o } > mem0
  
  .text.init1 : { *(.text.init1) } > mem1
  .text.core1 : { basic_core1.o(.text .text.*) } > mem1
  .text.mmio1 : { multicore_mmio1.o(.text .text.*) } > mem1
  .core1 : { basic_core1.o } > mem1
  .mmio1 : { multicore_mmio1.o } > mem1

   .text : { *(.text .text.*) } > mem2
  .data : { *(.data) } > mem2
  .bss : { *(.bss) } > mem2

  _end = .;
}




