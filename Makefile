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

KOIKA_LIB := ${OCAML_BUILD_DIR}/koika.cmxa
CUTTLEC_EXE := ${OCAML_BUILD_DIR}/cuttlec.exe

# FIXME: The ‘coq’ dependency is because dune doesn't track the dependency on
# Extraction.vo at the moment.  See https://github.com/ocaml/dune/issues/2178.
ocaml: coq
	@printf "\n== Building OCaml library and executables ==\n"
	dune build ocaml/cuttlec.exe ocaml/cuttlec.bc ocaml/koika.cma ocaml/koika.cmxa

# This prevents make from running two instances of Dune in parallel
${KOIKA_LIB} ${CUTTLEC_EXE}: ocaml;

PHONY += ocaml

####################
# Examples & tests #
####################

TESTS := $(wildcard tests/*.lv) $(wildcard tests/*.v)
EXAMPLES := $(wildcard examples/*.lv) $(wildcard examples/*.v) examples/rv/rv32i_core_pipelined.v

TESTS_TARGETS := $(patsubst %,%.objects/,${TESTS})
EXAMPLES_TARGETS := $(patsubst %,%.objects/,${EXAMPLES})

%.lv.objects/: %.lv ${CUTTLEC_EXE}
	@printf "\n-- Compiling %s --\n" "$<"
	@mkdir -p "$@"
	${CUTTLEC_EXE} "$<" \
		-T all -o "$@" $(if $(findstring .1.,$<),--expect-errors 2> "$@stderr")
	@touch "$@"

# The complexity below is due to lack of support in dune for OCaml files
# extracted from Coq, as well as the complexities of dependency tracking across
# folders in one repo.  In fact, the lines below are not even enough: the
# dependency from ‘examples/*.v’ on ‘coq/’ isn't captured, so one needs to call
# clean after updating files in ‘coq/’ to build examples without getting a
# ‘Compiled library … makes inconsistent assumptions over library …’ message.
#
# Code written against a packaged version of Koika (e.g. installed using OPAM)
# don't need to use these tricks; instead, you can just use the
# following commands:
#
#   ocamlfind ocamlopt -package koika.registry extracted.mli extracted.ml -shared -o extracted.cmxs
#   cuttlec extracted.cmxs -T verilog -o directory

%.v.objects/: %.v coq ${CUTTLEC_EXE}
	@printf "\n-- Compiling $< --\n"
# Set up variables                                                # examples/rv/xyz.v.objects/
	@$(eval DIR := $(dir $*))                                     # examples/rv/
	@$(eval MODNAME := $(notdir $*))                              # xyz
	@$(eval BUILT_VO := ${BUILD_DIR}/$*.vo)                       # _build/default/examples/rv/xyz.vo
	@$(eval BUILT_ML := ${BUILD_DIR}/$*.ml)                       # _build/default/examples/rv/xyz.ml
	@$(eval EXTRACTED_DIR := ${DIR}extracted)                     # examples/rv/extracted
	@$(eval BUILD_EXTRACTED_DIR := ${BUILD_DIR}/${EXTRACTED_DIR}) # _build/default/examples/rv/extracted
	@$(eval BUILT_CMXS := ${BUILD_EXTRACTED_DIR}/${MODNAME}.cmxs) # _build/default/examples/rv/extracted/xyz.cmxs
	@$(eval MAKEFILE_NAME := ${MODNAME}.mk)                       # xyz.v.mk
	@$(eval MAKEFILE_PATH := ${DIR}${MAKEFILE_NAME})              # examples/rv/xyz.v.mk
	@mkdir -p "$@" "${EXTRACTED_DIR}"
# Generate xyz.ml; coqdep will complain: see https://github.com/ocaml/dune/pull/2053
	@rm -f "${BUILT_VO}"
	dune build "$*.vo"
	@mv "${BUILT_ML}"* "${EXTRACTED_DIR}/"
# Generate a fresh dune file to build xyz.ml
	@ocaml etc/gen_dune.ml "${EXTRACTED_DIR}" > "${EXTRACTED_DIR}/dune"
# Generate xyz.cmxs
	dune build "${EXTRACTED_DIR}/${MODNAME}.cmxs"
# Compile to circuits
	${CUTTLEC_EXE} "${BUILT_CMXS}" -T all -o "$@"
# Remove the generated dune file to prevent errors if extracted ml files are later deleted
	@rm "${EXTRACTED_DIR}/dune"
# Execute example-specific follow-ups if any
	if test -f "${MAKEFILE_PATH}"; then	$(MAKE) -C "${DIR}" -f "${MAKEFILE_NAME}"; fi
	@touch "$@"

examples: ${EXAMPLES_TARGETS};
clean-examples:
	find examples/ -type d \( -name *.objects -or -name extracted \) -exec rm -r {} +

tests: ${TESTS_TARGETS};
clean-tests:
	find tests/ -type d \( -name *.objects -or -name extracted \) -exec rm -r {} +

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
