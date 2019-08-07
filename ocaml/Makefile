default:
	rm -f *.exe
	dune build cli.exe
	dune build collatz.exe

dot: default
	../_build/default/ocaml/collatz.exe | tee /dev/stderr | tee circuit.dot | dot -Tpng -o circuit.png

sim:
	g++ -O3 -Wall -Wextra main.cpp -o main.exe
