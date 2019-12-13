#*****************************************************************************
# bpred_j.S
#-----------------------------------------------------------------------------
# branch prediction micro benchmark

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

	li x8, 100 # i = 100
	li TESTNUM, 0

loopstart:
	j step1
	li TESTNUM, 1
step15: 
	j step16
	li TESTNUM, 16
step14: 
	j step15
	li TESTNUM, 15
step13: 
	j step14
	li TESTNUM, 14
step12: 
	j step13
	li TESTNUM, 13
step11: 
	j step12
	li TESTNUM, 12
step10: 
	j step11
	li TESTNUM, 11
step9:  
	j step10
	li TESTNUM, 10
step8:  
	j step9
	li TESTNUM, 9
step7:  
	j step8
	li TESTNUM, 8
step6:  
	j step7
	li TESTNUM, 7
step5:  
	j step6
	li TESTNUM, 6
step4:  
	j step5
	li TESTNUM, 5
step3:  
	j step4
	li TESTNUM, 4
step2:  
	j step3
	li TESTNUM, 3
step1:  
	j step2
	li TESTNUM, 2
step16:
	addi x8, x8, -1 # i--
	# IF (i != 0) goto loopstart
	bne x8, x0, loopstart

	# check TESTNUM
	beq TESTNUM, x0, pass
	j fail # something wrong during jumps


TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
