#define SET_ENCLAVE(rd, rs1) .word 0x0000000B | ((rd) << 7) | ((rs1) << 15)


/* if a1 = 0, do lookup; if a1 = 1, do add. */
/* No state saved between entries to enclave 1, stack pointer constant */
.section ".text.enclave2.bootloader"
  .globl _enclave2_bootloader
  .p2align 2
_enclave2_bootloader:
  la sp, _fstack2
  bnez a1,call_add_password
  beq a1,x0,call_lookup
  j clear_state

call_lookup:
  mv a0,a2
  call lookup
  j clear_state

call_add_password:
  mv a0,a2
  mv a1,a3
  call add_password
  j clear_state

clear_state:
  li sp,0
  /* li t0,0x1000  *//* TODO: remove this... temp */
  SET_ENCLAVE(12,0)
spin:
  j spin
