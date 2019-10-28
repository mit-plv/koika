OCAML_BUILD_DIR=../_build/default/ocaml
COQ_EXAMPLES=${OCAML_BUILD_DIR}/coq_examples.exe
CLI=${OCAML_BUILD_DIR}/cli.exe
ML=$(wildcard *.ml)
BEAR=bear -o examples/compile_commands.json

# FIXME: remove the @echo line below once the fix to
# https://github.com/ocaml/dune/issues/138 is released
build:
	dune build coq_examples.bc coq_examples.exe cli.bc cli.exe
	@echo Leaving directory \`$(abspath $(dir $(lastword $(PWD))))\'

dirs:
	mkdir -p examples/coq examples/lv

coq: build dirs
	${COQ_EXAMPLES}

coq-bear: build dirs
	${BEAR} ${COQ_EXAMPLES}

lv: build dirs
	set -x; for f in examples/*.lv; do ${CLI} "$$f" "examples/lv/$$(basename "$${f%.*}.all")"; done

dot: lv
	set -x; for f in examples/lv/*.dot; do dot "$$f" -Tpng -o "$${f%.*}.png"; done

sim-lint: coq-bear
	clang-tidy -checks=*,-llvm-header-guard,-cppcoreguidelines-pro-bounds-pointer-arithmetic,-cppcoreguidelines-pro-bounds-constant-array-index,-google-runtime-int,-google-readability-todo,-hicpp-use-auto,-modernize-use-auto,-fuchsia-default-arguments,-hicpp-member-init,-cppcoreguidelines-pro-type-member-init -header-filter=.* examples/coq/*.cpp

sim-diff:
	bash -c "diff -u <(clang-format examples/collatz.handwritten.hpp | sed -n '/IMPLEMENTATION/,\$$p') <(sed -n '/IMPLEMENTATION/,\$$p' examples/coq/.hpp)" | colordiff

clean:
	dune clean
	rm -rf examples/coq examples/lv
