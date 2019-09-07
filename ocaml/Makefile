default:
	rm -f *.exe
	dune build cli.exe collatz.exe decoder.exe pipeline.exe

dot: default
	../_build/default/ocaml/collatz.exe 2>&1 >/dev/null | tee collatz.dot | dot -Tpng -o collatz.png
	../_build/default/ocaml/decoder.exe 2>&1 >/dev/null | tee decoder.dot | dot -Tpng -o decoder.png
	../_build/default/ocaml/pipeline.exe 2>&1 >/dev/null | tee pipeline.dot | dot -Tpng -o pipeline.png

sim:
	g++ -O3 -Wall -Wextra main.cpp -o main.exe

sim-lint:
	clang-tidy -checks=*,-llvm-header-guard,-cppcoreguidelines-pro-bounds-pointer-arithmetic -header-filter=.* main.cpp

sim-diff:
	bash -c "diff -u <(clang-format collatz.handwritten.hpp | sed -n '/IMPLEMENTATION/,\$$p') <(sed -n '/IMPLEMENTATION/,\$$p' collatz.generated.hpp)" | colordiff
