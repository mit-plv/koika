
#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

	# Look at cache lines at 0x4000, 0x6000
	li x1, 0x04000
	li x2, 0x06000

	# Store some data into a single cache line
	# I -> M
	li x3, 0x100
	sw x3, 0(x1)
	# Write hit
	li x3, 0x101
	sw x3, 4(x1)

	# Now store some data into another cache line with the same index
	# M -> I -> M
	li x3, 0x200
	sw x3, 0(x2)
	# Write hit
	li x3, 0x201
	sw x3, 4(x2)

	# Now read the data
	# M -> I -> S
	lw x3, 0(x1)
	li x4, 0x100
	li TESTNUM, 1
	bne x4, x3, fail
	# Read hit
	lw x3, 4(x1)
	li x4, 0x101
	li TESTNUM, 2
	bne x4, x3, fail

	# Now add 0x0F0 to each entry in the current cache line
	# Read hit
	lw x3, 0(x1)
	addi x3, x3, 0x0F0
	# S -> M
	sw x3, 0(x1)
	# Read/Write hit
	lw x3, 4(x1)
	addi x3, x3, 0x0F0
	sw x3, 4(x1)

	# Now read from another cache line to evect the current cache line
	# M -> I -> S
	lw x3, 0(x2)
	li x4, 0x200
	li TESTNUM, 3
	bne x4, x3, fail
	# Read hit
	lw x3, 4(x2)
	li x4, 0x201
	li TESTNUM, 4
	bne x4, x3, fail

	# Now read the main cache line to check the previous additions
	# S -> I -> S
	lw x3, 0(x1)
	li x4, 0x1F0
	li TESTNUM, 5
	bne x4, x3, fail
	# Read hit
	lw x3, 4(x1)
	li x4, 0x1F1
	li TESTNUM, 6
	bne x4, x3, fail

	# If we get here then we passed
	j pass


TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
