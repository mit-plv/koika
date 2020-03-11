OUTPUT_ARCH("riscv")
ENTRY(_start)

#ifdef RV32E
_ADDRESS_WIDTH = 10; /* 4kiB of memory, 1kiB of stack */
#else
_ADDRESS_WIDTH = 16; /* 256kiB of memory, 64kiB of stack */
#endif

_MEMSIZE = (1 << _ADDRESS_WIDTH) * 4;
_MIN_STACK_SIZE = (1 << _ADDRESS_WIDTH);
_fstack = _MEMSIZE - 4;

MEMORY {
  bram (rx) : ORIGIN = 0x0, LENGTH = _MEMSIZE - _MIN_STACK_SIZE
}

SECTIONS
{
  . = 0x00000000;
  .text.init : { *(.text.init) } > bram
  .text : { *(.text) } > bram
  .data : { *(.data) } > bram
  .bss : { *(.bss) } > bram
  _end = .;
}
