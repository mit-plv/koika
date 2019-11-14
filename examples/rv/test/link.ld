OUTPUT_ARCH( "riscv" )
 ENTRY( main )
 SECTIONS
 {
 /* text: test code section */
 . = 0x200;
 .text.init : { init.o(.text) }
 .text :
 {
 intermediate.o(.text)
 }
 /* data: Initialized data segment */
 .data :
 {
 intermediate.o(.data)
 }
 /* End of uninitialized data segment */
 _end = .;
 }

