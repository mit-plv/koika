#!/bin/bash
mkdir -p _build
bsc -aggressive-conditions +RTS -K16M -RTS -bdir _build -verilog -u -g top top.bsv && mv top.v ../
