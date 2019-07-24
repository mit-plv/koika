default:
	rm -f *.exe
	dune build cli.exe
	dune build collatz.exe

dot: driver.exe
	../_build/default/ocaml/driver.exe | tee /dev/stderr | tee circuit.dot | dot -Tpng -o circuit.png
