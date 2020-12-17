#!/usr/bin/env bash
## Compile a Bluespec design with Verilator
DUT=$1
rm -fr bsv.obj_dir.opt
set -x
verilator ${@:2} \
    -CFLAGS -DVL_USER_FINISH -Wno-fatal \
    --prefix V$DUT --cc --exe --compiler gcc \
    --Mdir bsv.obj_dir.opt \
    --x-assign fast --x-initial fast --noassert -O3 \
    -CFLAGS '-O3 -march=native -U_FORTIFY_SOURCE -D_FORTIFY_SOURCE=0 -fno-stack-protector -flto' \
    -LDFLAGS '-O3 -march=native -U_FORTIFY_SOURCE -D_FORTIFY_SOURCE=0 -fno-stack-protector -flto' \
    "$DUT"_verilator.cpp $DUT.v
make -C bsv.obj_dir.opt -f V$DUT.mk V$DUT
