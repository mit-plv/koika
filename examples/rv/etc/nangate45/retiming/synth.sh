#!/usr/bin/env bash
# Use yosys to synthesize ASIC circuits against Nangate45 (PLDI 2019)

set -e

export ABC_LIBFILE=NangateOpenCellLibrary_fast_ccs.lib

if [ ! -f $ABC_LIBFILE ]; then
	echo "Library file NangateOpenCellLibrary_fast_ccs.lib (part of NangateOpenCellLibrary_PDKv1_3_v2010_12) not found."
	echo "You can download a copy for non-commercial use at http://projects.si2.org/openeda.si2.org/projects/nangatelib"
	exit 1
fi

export YOSYS_LIBDIR=../
export BSV_TOP=rv32i_bsv
export KOIKA_TOP=rv32

echo "== Using Nangate Open Cell Library (v1_3_v2010_12) =="

echo "-- Running synthesis for BSV design --"
export VERILOG_INPUT=../$BSV_TOP.v
export VERILOG_TOP=$BSV_TOP
yosys -v8 -c nangate45-retiming.tcl -l $BSV_TOP.log || true # PLDI_FIXME(CPC)

echo "-- Running synthesis for Kôika design --"
export VERILOG_INPUT=../$KOIKA_TOP.v
export VERILOG_TOP=$KOIKA_TOP
yosys -v8 -c nangate45-retiming.tcl -l $KOIKA_TOP.log

echo "======================="
echo "== Synthesis results =="
echo "======================="
echo BSV:   "$(grep Delay $BSV_TOP.log)"
echo Kôika: "$(grep Delay $KOIKA_TOP.log)"
