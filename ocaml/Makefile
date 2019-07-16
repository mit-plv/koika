driver.exe:
	rm -f driver.exe
	dune build driver.exe

dot: driver.exe
	../_build/default/ocaml/driver.exe | tee /dev/stderr | tee circuit.dot | dot -Tpng -o circuit.png
