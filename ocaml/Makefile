default:
	rm -f *.exe
	dune build cli.exe collatz.exe decoder.exe pipeline.exe

dot: default
	../_build/default/ocaml/collatz.exe && dot -Tpng -o collatz.png
	../_build/default/ocaml/decoder.exe && dot -Tpng -o decoder.png
	../_build/default/ocaml/pipeline.exe && dot -Tpng -o pipeline.png

sim:
	g++ -O3 -Wall -Wextra main.cpp -o main.exe

sim-lint:
	clang-tidy -checks=*,-llvm-header-guard,-cppcoreguidelines-pro-bounds-pointer-arithmetic,-cppcoreguidelines-pro-bounds-constant-array-index,-google-runtime-int,-google-readability-todo,-hicpp-use-auto,-modernize-use-auto -header-filter=.* main.cpp

sim-diff:
	bash -c "diff -u <(clang-format collatz.handwritten.hpp | sed -n '/IMPLEMENTATION/,\$$p') <(sed -n '/IMPLEMENTATION/,\$$p' collatz.generated.hpp)" | colordiff
