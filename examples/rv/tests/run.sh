#!/usr/bin/env bash
## Run a RISCV test
sim=$1
binary=$2
args=(${@:3})
TIMEFORMAT=$'  real: %3lR\tuser: %3lU\tsys: %3lS'

echo "./$(basename "$sim") $(basename "$binary")"

case $binary in
    *.rv32)
        echo "  $sim $binary" -1
        time "$sim" "$binary" -1 "${args[@]}"
        case $? in
            0) echo "  [0;32mPASS[0m";;
            *) echo "  [0;31mFAIL[0m ($?)";;
        esac;;
    *.vmh) # top.v expects the memory in mem.vmh
        sim_name=$(basename "$sim")
        sim_dir=$(dirname "$(realpath --relative-to=. "$sim")")
        vmh_path=$(realpath --relative-to="$sim_dir" "$binary")
        echo "  ln -f -s $vmh_path mem.vmh && ./$sim_name -1 ${args[*]}"
        cd "$sim_dir" && ln -f -s "$vmh_path" mem.vmh && time "./$sim_name" -1  "${args[@]}";;
esac
