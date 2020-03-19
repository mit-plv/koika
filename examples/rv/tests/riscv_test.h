// See LICENSE for license details.

#ifndef _ENV_PHYSICAL_SINGLE_CORE_H
#define _ENV_PHYSICAL_SINGLE_CORE_H

#include "encoding.h"

//-----------------------------------------------------------------------
// Begin Macro
//-----------------------------------------------------------------------

#define RVTEST_RV32U                                                    

#define RVTEST_CODE_BEGIN                                               \
        .text;                                                          \
        .align  6;                                                      \
        .globl _start;                                                  \
_start:                                                                 


//-----------------------------------------------------------------------
// TESTNUM reg Macro
//-----------------------------------------------------------------------

#define TESTNUM x28 // t3

//-----------------------------------------------------------------------
// Print Macro
//-----------------------------------------------------------------------

#define PRINT_NEWLINE(tmp_reg_1, tmp_reg_2)                             \
        li tmp_reg_1, 0x0000000A;                                       \
        li tmp_reg_2, 0x40000000;                                       \
        sw tmp_reg_1, 0(tmp_reg_2);

#define PRINT_INT(arg_reg, tmp_reg)                                     \
        li tmp_reg, 0x40000000;                                         \
        sw arg_reg, 4(tmp_reg);

//-----------------------------------------------------------------------
// End Macro (return value in TESTNUM)
// TESTNUM always < 65536 here, so no need to set ExitCode on MSB
// we print cycle (1st line) & instruction (2nd line)
//-----------------------------------------------------------------------

#define RVTEST_CODE_END                                                 \
exit:   li a0, 0x40001000;                                              \
        sw TESTNUM, 0(a0);                                              \
1:      j 1b

//-----------------------------------------------------------------------
// Pass/Fail Macro (TESTNUM stores the return value)
// Pass: return 0
// Fail: return failed test id (already in TESTNUM)
//-----------------------------------------------------------------------

#define RVTEST_PASS                                                     \
        li TESTNUM, 0;                                                  \
        j exit

#define RVTEST_FAIL                                                     \
        j exit

//-----------------------------------------------------------------------
// Data Section Macro
//-----------------------------------------------------------------------

#define EXTRA_DATA

#define RVTEST_DATA_BEGIN EXTRA_DATA .align 4; .global begin_signature; begin_signature:
#define RVTEST_DATA_END .align 4; .global end_signature; end_signature:

#endif
