#!/usr/bin/env bash
## Yosys synthesis script for Nangate Open Cell Library (45nm)

set -e

export ABC_LIBFILE=NangateOpenCellLibrary_fast_ccs.lib

if [ ! -f $ABC_LIBFILE ]; then
	echo "Library file NangateOpenCellLibrary_fast_ccs.lib (part of NangateOpenCellLibrary_PDKv1_3_v2010_12) not found."
	echo "You can download a copy for non-commercial use at http://projects.si2.org/openeda.si2.org/projects/nangatelib"
	exit 1
fi

if [ ! -d "$SCRIPT_DIR" ]; then
    echo "SYNTH_MODE not set to one of $(ls -d */ | cut -f1 -d'/' | xargs)"
    exit 1
fi

export KOIKA_TOP=rv32
export BSV_TOP=rv32_bsv

export KOIKA_LIBDIR=$(realpath --relative-to "$SCRIPT_DIR" ../)
export BSV_LIBDIR=$(realpath --relative-to "$SCRIPT_DIR" ../bsv/rv32_bsv/)
ln -s -f "$(realpath $ABC_LIBFILE)" "$SCRIPT_DIR"

cd "$SCRIPT_DIR"
echo "In directory $PWD"

echo "== Using Nangate Open Cell Library (v1_3_v2010_12) =="

YOSYS_DEFINES="-DMEM_FILENAME=\"../../../../tests/_build/$DUT/integ/primes.vmh\""

echo "----------------------------------------"
echo "-- Running synthesis for Kôika design --"
echo "----------------------------------------"
export VERILOG_TOP=$KOIKA_TOP
export YOSYS_LIBDIR=$KOIKA_LIBDIR
export VERILOG_INPUT=$YOSYS_LIBDIR/$VERILOG_TOP.v
yosys -v8 "$YOSYS_DEFINES" -c synth.tcl -l $VERILOG_TOP.log

echo "--------------------------------------"
echo "-- Running synthesis for BSV design --"
echo "--------------------------------------"
export VERILOG_TOP=$BSV_TOP
export YOSYS_LIBDIR=$BSV_LIBDIR
export VERILOG_INPUT=$YOSYS_LIBDIR/$VERILOG_TOP.v
yosys -v8 "$YOSYS_DEFINES" -c synth.tcl -l $VERILOG_TOP.log || true

echo "======================="
echo "== Synthesis results =="
echo "======================="
echo Kôika: "$(grep Delay $KOIKA_TOP.log)"
echo BSV:   "$(grep Delay $BSV_TOP.log)"
