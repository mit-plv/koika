#!/usr/bin/env bash
sim=$1
prog=$2
TIMEFORMAT=$'  real: %3lR\tuser: %3lU\tsys: %3lS'

echo "- $(basename "$sim") $prog"

case $prog in
    *.rv32)
        time "$sim" "$prog" -1
        case $? in
            0) echo "  [0;32mPASS[0m";;
            *) echo "  [0;31mFAIL[0m";;
        esac;;
    *.vmh) # mkProc.v expected the memory in mem.vmh
        sim_dir=$(dirname "$(realpath "$sim")")
        ln -f -s "$(realpath "$prog")" "$sim_dir/mem.vmh";
        # The verilator driver always returns 0
        time (cd "$sim_dir" || exit 1; "./$(basename "$sim")" -1);;
esac

