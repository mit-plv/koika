#!/bin/bash
mkdir -p _build
bsc -aggressive-conditions +RTS -K16M -RTS -bdir _build -verilog -u -g top_bsv top_bsv.bsv
bsc -aggressive-conditions +RTS -K16M -RTS -bdir _build -verilog -u -g rv32_bsv rv32_bsv.bsv
verilator -Wno-fatal -O3 -CFLAGS -O3 -cc --exe top_bsv.v driver.cpp 
make -C obj_dir -f Vtop_bsv.mk -j 4
#g++ -O3 -I obj_dir -I/usr/share/verilator/include  /usr/share/verilator/include/verilated.cpp driver.cpp -o module obj_dir/Vtop_bsv__ALL.a


bsc -aggressive-conditions +RTS -K16M -RTS -bdir _build -sim -u -g rv32_bsv rv32_bsv.bsv
bsc -aggressive-conditions +RTS -K16M -RTS -bdir _build -sim -u -g top_bsv top_bsv.bsv
bsc -bdir _build -sim -e top_bsv
