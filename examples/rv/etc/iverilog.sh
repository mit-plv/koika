#!/usr/bin/env sh
## Simulate the core with Icarus Verilog

test=$1
tmp=$(mktemp)

echo +define+BROKEN_READMEMH \
     +define+MEM_ADDRESS_WIDTH=14 \
     +define+MEM_FILENAME='"'"$test"'"' \
     +define+SIMULATION \
     > $tmp

set -x
iverilog memory.v ext_finish.v ext_mem.v rv32.v top.v testbench.v -o iverilog.vvp \
         -c $tmp || exit
