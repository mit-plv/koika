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
	rm -f ${COQ_BUILD_DIR}/Extraction.vo; dune build coq/Extraction.vo
	cp ${COQ_BUILD_DIR}/extracted.ml ocaml/cuttlebone/extr.ml
	cp ${COQ_BUILD_DIR}/extracted.mli ocaml/cuttlebone/extr.mli

coq-all:
	dune build @coq/all

PHONY += coq coq-all

#########
# OCaml #
#########

KOIKA_LIB := ${OCAML_BUILD_DIR}/koika.cmxa
COQ_DEMO_EXE := ${OCAML_BUILD_DIR}/demo.exe
CUTTLEC_EXE := ${OCAML_BUILD_DIR}/cuttlec.exe

# FIXME: remove the @echo line below once the fix to
# https://github.com/ocaml/dune/issues/138 is released
# FIXME: The coq dependency is because dune doesn't track the dependency on
# Extraction.vo at the moment.
ocaml: coq
	dune build ocaml/demo.exe ocaml/demo.bc ocaml/cuttlec.exe ocaml/cuttlec.bc ocaml/koika.cma ocaml/koika.cmxa
	@echo Leaving directory \`$(abspath $(dir $(lastword $(PWD))))\'

# This prevents make from running two instances of Dune in parallel
${COQ_DEMO_EXE} ${CUTTLEC_EXE}: ocaml;

PHONY += ocaml

####################
# Examples & tests #
####################

TESTS := $(wildcard tests/*.lv) $(wildcard tests/*.v)
EXAMPLES := $(wildcard examples/*.lv) examples/collatz.lv

TESTS_TARGETS := $(patsubst %,%.objects/,${TESTS})
EXAMPLES_TARGETS := $(patsubst %,%.objects/,${EXAMPLES})

%.lv.objects/: %.lv ${CUTTLEC_EXE}
	mkdir -p "$<.objects"
	${CUTTLEC_EXE} 2> "$@stderr" "$<" -T all -o "$@" || true
	touch "$@"

%.v.objects/: %.v coq ${CUTTLEC_EXE}
# Set up variables                                               @# examples/rv/xyz.v.objects/_built
	$(eval MODNAME := $(notdir $*))                              @# xyz
	$(eval BUILT_VO := ${BUILD_DIR}/$*.vo)                       @# _build/default/examples/rv/xyz.vo
	$(eval BUILT_ML := ${BUILD_DIR}/$*.ml)                       @# _build/default/examples/rv/xyz.ml
	$(eval EXTRACTED_DIR := $(dir $*)extracted)                 @# examples/rv/extracted
	$(eval BUILD_EXTRACTED_DIR := ${BUILD_DIR}/${EXTRACTED_DIR}) @# _build/default/examples/rv/extracted
	$(eval BUILT_CMXS := ${BUILD_EXTRACTED_DIR}/${MODNAME}.cmxs) @# _build/default/examples/rv/extracted/xyz.cmxs
	mkdir -p "$@" "${EXTRACTED_DIR}"
# Generate xyz.ml
	rm -f "${BUILT_VO}"; dune build "$*.vo"
	mv "${BUILT_ML}"* "${EXTRACTED_DIR}/"
# Generate a fresh dune file to build xyz.ml
	ocaml etc/gen_dune.ml "${EXTRACTED_DIR}" > "${EXTRACTED_DIR}/dune"
# Generate xyz.cmxs
	dune build "${EXTRACTED_DIR}/${MODNAME}.cmxs"
# Compile to circuits
	${CUTTLEC_EXE} 2> "$@stderr" "${BUILT_CMXS}" -T all -o "$@" || true
# Clean up
	rm "${EXTRACTED_DIR}/dune" # Prevent errors if extracted ml files are later deleted
	touch "$@"

examples/demo.v.objects/: ${COQ_DEMO_EXE}
	mkdir -p "$@"
	${COQ_DEMO_EXE}
	touch "$@"

examples: ${EXAMPLES_TARGETS} ${COQ_DEMO_TARGET}
clean-examples:
	find examples/ -type d \( -name *.objects -or -name extracted \) -exec rm -r {} +

tests: ${TESTS_TARGETS}
clean-tests:
	find tests/ -type d \( -name *.objects -or -name extracted \) -exec rm -r {} +

PHONY += examples clean-examples tests clean-tests

#################
# Whole project #
#################

all: coq ocaml examples tests
	dune build @all

clean: clean-tests clean-examples
	dune clean

PHONY += all clean

.PHONY: ${PHONY}
.SUFFIXES:
