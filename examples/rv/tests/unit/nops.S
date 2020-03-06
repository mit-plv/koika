#include "../riscv_tests/riscv_test.h"
#include "../riscv_tests/test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    RVTEST_PASS

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
