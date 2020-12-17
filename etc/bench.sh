#!/usr/bin/env bash

REPEAT=10
GCC=g++-9

bench() {
    compiler=$1
    simulator=$2
    input=$3
    { export TIMEFORMAT=$'\n''>> '$compiler$'\t'$simulator$'\t'$input$'\treal: %3R\tuser: %3U\tsys: %3S'; } 2> /dev/null
    echo "<< $simulator $input"
    for _ in $(seq 1 $REPEAT); do
        time ${@:4}
    done
}

declare -A DESIGN_TESTS
DESIGN_TESTS[rv32i]=rv32i
DESIGN_TESTS[rv32e]=rv32e
DESIGN_TESTS[rv32i-bp]=rv32i
DESIGN_TESTS[rv32i-mc]=rv32i_no_sm

bench_rv_1 () {
    root=$1
    compiler=$2
    simulator=$3
    design=$4
    test=$5

    verilator=$(realpath bench/verilator.sh)
    base=$(realpath $root/_objects/$design.v/)
    # Find tests after resolving simlinks in base
    tests=$(realpath $base/../../tests/_build/${DESIGN_TESTS[$design]}/integ/)
    b="bench $compiler $simulator $design-$test"

    make -C $base clean
    case $simulator in
        cuttlesim)
            make CXX=$compiler -C $base rvcore.cuttlesim.opt
            $b $base/rvcore.cuttlesim.opt $tests/$test.rv32 -1;;
        verilator-koika)
            make CXX=$compiler -C $base obj_dir.opt/Vtop
            $b $base/obj_dir.opt/Vtop +VMH=$tests/$test.vmh -1;;
        cvc)
            (cd $base; ./cvc64.sh $tests/$test.vmh; $b ./cvc64.opt);;
        icarus)
            (cd $base; ./iverilog.sh $tests/$test.vmh; $b ./iverilog.vvp);;
        verilator-bluespec)
            (cd $base/bsv/rv32_bsv/;
             rm -fr bsv.obj_dir.opt;
             $verilator top_bsv +define+BRAM_RUNTIME_INIT +define+SIMULATION)
            $b $base/bsv/rv32_bsv/bsv.obj_dir.opt/Vtop_bsv +VMH=$tests/$test.vmh -1;;
    esac
}

bench_rv_rooted () {
    for simulator in ${@:4}; do
        bench_rv_1 $1 $GCC $simulator ${@:2:3}
    done
}

ROOT=$(realpath ../examples/rv/)

bench_rv () {
    bench_rv_rooted $ROOT ${@:1}
}

bench_compilers () {
    for compiler in "clang++-10" "g++-10"; do
        for simulator in ${@:3}; do
            bench_rv_1 $ROOT $compiler $simulator ${@:1:2}
        done
    done
}

bench_comb_1 () {
    compiler=$1
    simulator=$2
    design=$3
    cycles=$4

    base=$(realpath ../examples/_objects/$design.v/)
    verilator=$(realpath bench/verilator.sh)
    bsv=mk$design
    b="bench $compiler $simulator $design"

    make -C $base clean
    case $simulator in
        cuttlesim)
            make CXX=$compiler -C $base $design.opt
            $b $base/$design.opt $cycles;;
        verilator-koika)
            make CXX=$compiler -C $base obj_dir.opt/V$design
            $b $base/obj_dir.opt/V$design $cycles;;
        verilator-bluespec)
            (cd $base/; $verilator $bsv)
            $b $base/bsv.obj_dir.opt/V$bsv $cycles;;
    esac
}

bench_comb () {
    for simulator in ${@:3}; do
        bench_comb_1 $GCC $simulator ${@:1:2}
    done
}

# cd $(realpath "$(dirname "${BASH_SOURCE[0]}")/..")
# export PATH="/build/open-src-cvc/src/:$PATH"

# set -x

SIMS="cuttlesim verilator-koika"
bench_comb collatz 1000000000 $SIMS
SIMS="cuttlesim verilator-koika verilator-bluespec"
bench_comb fir 1000000000 $SIMS
bench_comb fft 30000000 $SIMS

SIMS="cuttlesim verilator-koika verilator-bluespec"
bench_rv rv32i primes $SIMS
SIMS="cuttlesim verilator-koika"
bench_rv rv32e primes $SIMS
bench_rv rv32i-bp primes $SIMS
bench_rv rv32i-mc primes $SIMS
bench_compilers rv32i primes $SIMS
bench_compilers rv32e primes $SIMS
