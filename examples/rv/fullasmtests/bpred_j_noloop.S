#*****************************************************************************
# bpred_j.S
#-----------------------------------------------------------------------------
# branch prediction micro benchmark

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

	li TESTNUM, 0

	j step1
	li TESTNUM, 1
step31:
	j step32
	li TESTNUM, 32
step30:
	j step31
	li TESTNUM, 31
step29:
	j step30
	li TESTNUM, 30
step28:
	j step29
	li TESTNUM, 29
step27:
	j step28
	li TESTNUM, 28
step26:
	j step27
	li TESTNUM, 27
step25:
	j step26
	li TESTNUM, 26
step24:
	j step25
	li TESTNUM, 25
step23:
	j step24
	li TESTNUM, 24
step22:
	j step23
	li TESTNUM, 23
step21:
	j step22
	li TESTNUM, 22
step20:
	j step21
	li TESTNUM, 21
step19:
	j step20
	li TESTNUM, 20
step18:
	j step19
	li TESTNUM, 19
step17:
	j step18
	li TESTNUM, 18
step16:
	j step17
	li TESTNUM, 17
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
step32:
	# check TESTNUM
	beq TESTNUM, x0, pass
	j fail # something wrong during jumps


TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
