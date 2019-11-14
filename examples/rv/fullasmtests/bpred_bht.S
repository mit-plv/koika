#*****************************************************************************
# bpred_bht.S
#-----------------------------------------------------------------------------
# branch prediction micro benchmark
# A bht will improve the prediction of branches 1-4 over just a btb

# XXX: "# if" will become macro testing, will not be a comment


#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

	li a0, 100 # i = 100
	li TESTNUM, 0
	# some constants
	li a2, 1
	li a3, 2
	li a4, 3

loopstart:
	# v = i & 0x03
	andi a1, a0, 3 
	# IF(v != 0) TESTNUM++
	beq a1, x0, skip0
	addi TESTNUM, TESTNUM, 1
skip0:
	# IF(v != 1) TESTNUM++
	beq a1, a2, skip1
	addi TESTNUM, TESTNUM, 1
skip1:
	# IF(v != 2) TESTNUM++
	beq a1, a3, skip2
	addi TESTNUM, TESTNUM, 1
skip2:
	# IF(v != 3) TESTNUM++
	beq a1, a4, skip3
	addi TESTNUM, TESTNUM, 1
skip3:
	# i--
	addi a0, a0, -1 
	# IF(i != 0) goto loopstart
	bne a0, x0, loopstart 

	# check result of TESTNUM (should be 300)
	li a0, 300
	beq TESTNUM, a0, pass
	j fail # error, return wrong TESTNUM value

TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
