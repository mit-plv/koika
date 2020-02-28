#!/bin/bash
mkdir -p _build
bsc -aggressive-conditions +RTS -K16M -RTS -bdir _build -verilog -u -g top_bsv top_bsv.bsv
bsc -aggressive-conditions +RTS -K16M -RTS -bdir _build -verilog -u -g rv32_bsv rv32_bsv.bsv
