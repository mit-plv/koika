default:
	rm -f *.exe
	dune build cli.exe
	dune build collatz.exe

dot: default
	../_build/default/ocaml/collatz.exe | tee /dev/stderr | tee circuit.dot | dot -Tpng -o circuit.png

sim:
	g++ -O3 -Wall -Wextra main.cpp -o main.exe

sim-lint:
	clang-tidy -checks=*,-llvm-header-guard,-cppcoreguidelines-pro-bounds-pointer-arithmetic -header-filter=.* main.cpp

sim-diff:
	bash -c "diff -u <(clang-format collatz.handwritten.hpp | sed -n '/IMPLEMENTATION/,\$$p') <(sed -n '/IMPLEMENTATION/,\$$p' collatz.generated.hpp)" | colordiff
