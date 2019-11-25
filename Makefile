BUILD_DIR := _build/default
COQ_BUILD_DIR := ${BUILD_DIR}/coq
OCAML_BUILD_DIR := ${BUILD_DIR}/ocaml
PHONY :=

default: all

#######
# Coq #
#######

# FIXME: These ‘cp’ calls shouldn't be needed; see
# https://discuss.ocaml.org/t/4462/
coq:
	@printf "\n== Building Coq library ==\n"
	@rm -f ${COQ_BUILD_DIR}/Extraction.vo
	dune build coq/Extraction.vo coq/Std.vo
	@cp ${COQ_BUILD_DIR}/extracted.ml ocaml/cuttlebone/extr.ml
	@cp ${COQ_BUILD_DIR}/extracted.mli ocaml/cuttlebone/extr.mli

coq-all:
	@printf "\n== Building Coq proofs ==\n"
	dune build @coq/all

PHONY += coq coq-all

#########
# OCaml #
#########

# FIXME: The ‘coq’ dependency is because dune doesn't track the dependency on
# Extraction.vo at the moment.  See https://github.com/ocaml/dune/issues/2178.
ocaml: coq
	@printf "\n== Building OCaml library and executables ==\n"
	dune build ocaml/cuttlec.exe ocaml/cuttlec.bc @install

PHONY += ocaml

####################
# Examples & tests #
####################

TESTS := $(wildcard tests/*.lv) $(wildcard tests/*.v)
EXAMPLES := $(wildcard examples/*.lv) $(wildcard examples/*.v) examples/rv/rv32i_core_pipelined.v

TESTS_TARGETS := $(patsubst %,%.objects/,${TESTS})
EXAMPLES_TARGETS := $(patsubst %,%.objects/,${EXAMPLES})

%.lv.objects/: %.lv ocaml
	@printf "\n-- Compiling %s --\n" "$<"
	@mkdir -p "$@"
	dune exec cuttlec -- "$<" \
		-T all -o "$@" $(if $(findstring .1.,$<),--expect-errors 2> "$@stderr")
	@touch "$@"

# Dune can't track multi-library Coq dependencies, so the dependency from
# ‘examples/*.v’ on ‘coq/’ isn't captured.  As a result, one needs to call
# ‘clean’ after updating files in ‘coq/’ to build examples without getting a
# ‘Compiled library … makes inconsistent assumptions over library …’ message.
#
# Code written against a packaged version of Koika (e.g. installed using OPAM)
# won't run into this issue; you can just use the following command:
#
#   cuttlec extracted.ml -T verilog -o directory

%.v.objects/: %.v coq ocaml
	@printf "\n-- Compiling $< --\n"
	@mkdir -p "$@"
# Set up variables                                                # examples/rv/xyz.v.objects/
	@$(eval DIR := $(dir $*))                                     # examples/rv/
	@$(eval MAKEFILE_NAME := $(notdir $*).mk)                     # xyz.v.mk
# Generate xyz.ml; coqdep will complain: see https://github.com/ocaml/dune/pull/2053
	@rm -f "${BUILD_DIR}/$*.vo"
	dune build "$*.vo"
# Compile to circuits
	dune exec cuttlec -- "${BUILD_DIR}/$*.ml" -T all -o "$@"
# Execute example-specific follow-ups if any
	cd ${DIR}; if test -f "${MAKEFILE_NAME}"; then $(MAKE) -f "${MAKEFILE_NAME}"; fi
	@touch "$@"

examples: ${EXAMPLES_TARGETS};
clean-examples:
	find examples/ -type d -name *.objects -exec rm -r {} +
	rm -rf ${BUILD_DIR}/examples

tests: ${TESTS_TARGETS};
clean-tests:
	find tests/ -type d -name *.objects -exec rm -r {} +
	rm -rf ${BUILD_DIR}/tests

PHONY += examples clean-examples tests clean-tests

#################
# Whole project #
#################

all: coq ocaml examples tests
	@printf "\n== Completing full build ==\n"
	dune build @all

clean: clean-tests clean-examples
	dune clean

PHONY += all clean

.PHONY: ${PHONY}
.SUFFIXES:

# Running two copies of dune in parallel isn't safe, and dune is already
# handling most of the parallelism for us
.NOTPARALLEL:
