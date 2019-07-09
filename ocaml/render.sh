#!/usr/bin/env sh
ocamlc sga.mli sga.ml driver.ml -o driver.exe && (./driver.exe | tee /dev/stderr | tee circuit.dot | dot -Tpng -o circuit.png)
