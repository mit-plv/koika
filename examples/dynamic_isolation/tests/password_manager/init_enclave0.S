#include "encoding.h"

#define LREG lw
#define SREG sw
#define REGBYTES 4

#define SET_ENCLAVE(rd, rs1) .word 0x0000000B | ((rd) << 7) | ((rs1) << 15)

.section ".text.enclave0.init"
#  .text
#  .align 6
  .globl _start
_start:
  li  x1, 0
  li  x2, 0
  li  x3, 0
  li  x4, 0
  li  x5, 0
  li  x6, 0
  li  x7, 0
  li  x8, 0
  li  x9, 0
  li  x10,0
  li  x11,0
  li  x12,0
  li  x13,0
  li  x14,0
  li  x15,0
  li  x16,0
  li  x17,0
  li  x18,0
  li  x19,0
  li  x20,0
  li  x21,0
  li  x22,0
  li  x23,0
  li  x24,0
  li  x25,0
  li  x26,0
  li  x27,0
  li  x28,0
  li  x29,0
  li  x30,0
  li  x31,0

  la sp, _fstack0
  la a0, call_main
  call save_enclave_state

  call bootloader
spin:
  j spin

.section ".text.enclave0.bootloader"
   .p2align 2
#  .text
#  .align 6
bootloader:
  la t0,_glbl0
  lw sp,0(t0) #load t1 in stack
  lw x6,0(sp)
  addi sp,sp,4
  jalr x6
  li x10, 0
  call exit0
  ret

.section ".text.enclave0.main"
  .p2align 2
call_main:
  addi sp, sp,-4
  sw   ra,0(sp)
  call main0
  lw   ra,0(sp)
  addi sp,sp,4
  ret

save_enclave_state:
  addi sp,sp,-4
  sw   a0,0(sp) # save next pc
  la   t0,_glbl0 #sp address
  sw   sp, 0(t0)
  ret

  .p2align 2
  .type    set_enclave,%function

/*  .type    set_enclave,%function*/
# TODO: does not follow RISC-V conventions oops. Need to save nore regusters,
set_enclave: # arg: a0 := enclave_id; a1 := func_code; a2-a7 := arguments
  addi sp, sp,-4
  sw   ra,0(sp)
  mv   s2,a0
  auipc a0,0
  /*addi a0,a0,24 # pc+24 ; TODO: change to 20 when removing temp instruction*/
  addi a0,a0,20 # pc+24 ; TODO: change to 20 when removing temp instruction
  call save_enclave_state
  mv   a0,s2
  /*li   t0,0x10001000  /* TODO: remove this... temp */
  SET_ENCLAVE(10,10) #set_enclave a0,a0
  lw   ra,0(sp)
  addi sp,sp,4
  ret

  .globl _lookup
  .type  _lookup,%function
_lookup:
  addi sp,sp,-4
  sw ra,0(sp)
  mv a2,a0
  li a0,2
  li a1,0
  call set_enclave
  lw ra,0(sp)
  addi sp,sp,4
  ret

  .globl _add_password
  .type  _add_password,%function
_add_password:
  addi sp,sp,-4
  sw ra,0(sp)
  mv a2,a0
  mv a3,a1
  li a0,2
  li a1,1
  call set_enclave
  lw ra,0(sp)
  addi sp,sp,4
  ret

#.section ".tdata.begin"
#.globl _tdata_begin
#_tdata_begin:
#
#.section ".tdata.end"
#.globl _tdata_end
#_tdata_end:
#
#.section ".tbss.end"
#.globl _tbss_end
#_tbss_end:
