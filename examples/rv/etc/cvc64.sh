#!/usr/bin/env sh
## Simulate the core with CVC

test=$1
OPT='-O +2state +notimingchecks +mipdopt +nbaopt'

set -x
cvc64 $OPT \
      +define+BROKEN_READMEMH \
      +define+STDERR="32'd2" \
      +define+MEM_ADDRESS_WIDTH=14 \
      +define+MEM_FILENAME='"'"$test"'"' \
      +define+SIMULATION \
      memory.v ext_finish.v ext_mem.v rv32.v top.v testbench.v \
      -o cvc64.opt || exit

# OPT='+dumpvars +interp +define+DUMPFLUSH'
# gtkwave -A --optimize --stems obj_dir.opt/*stems verilog.dump
