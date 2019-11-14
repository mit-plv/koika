#*****************************************************************************
# bpred_ras.S
#-----------------------------------------------------------------------------
# branch prediction micro benchmark
# This benchmark stress tests return address stacks

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

	# we don't loop here, otherwise BTB will do a good job
	jal f1
	
	# check TESTNUM
	beq TESTNUM, x0, pass
	j fail

	
	# function calls
f1:
	addi s1, ra, 0
	li TESTNUM, 2
	jal f2
	li TESTNUM, 7
	jal f2
	addi ra, s1, 0
	jr ra

f2:
	addi s2, ra, 0
	li TESTNUM, 3
	jal f3
	li TESTNUM, 8
	jal f3
	addi ra, s2, 0
	jr ra

f3:
	addi s3, ra, 0
	li TESTNUM, 4
	jal f4
	li TESTNUM, 9
	jal f4
	addi ra, s3, 0
	jr ra

f4:
	addi s4, ra, 0
	li TESTNUM, 5
	jal f5
	li TESTNUM, 10
	jal f5
	addi ra, s4, 0
	jr ra

f5:
	addi s5, ra, 0
	li TESTNUM, 6
	jal f6
	li TESTNUM, 11
	jal f6
	addi ra, s5, 0
	jr ra

f6:
	li TESTNUM, 0
	jr ra



TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
