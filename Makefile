BUILD_DIR := _build/default
COQ_BUILD_DIR := ${BUILD_DIR}/coq
OCAML_BUILD_DIR := ${BUILD_DIR}/ocaml
PHONY :=

default: examples

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

COOKIE:=_built
LV_EXAMPLES := $(wildcard examples/*.lv)
LV_EXAMPLES_TARGETS := $(patsubst %.lv,%.lv.objects/${COOKIE},${LV_EXAMPLES})
LV_TESTS := $(wildcard tests/*.lv)
LV_TESTS_TARGETS := $(patsubst %.lv,%.lv.objects/${COOKIE},${LV_TESTS})
COQ_DEMO_TARGET := examples/demo.v.objects

%.lv.objects/${COOKIE}: %.lv ${CUTTLEC_EXE}
	mkdir -p "$<.objects"
	${CUTTLEC_EXE} > "$<.objects/stderr" "$<" "$<.objects/$(notdir $*).all" || true
	touch "$@"

${COQ_DEMO_TARGET}: ${COQ_DEMO_EXE}
	${COQ_DEMO_EXE}

examples: ${LV_EXAMPLES_TARGETS} ${COQ_DEMO_TARGET}
clean-examples:
	rm -rf examples/*.objects/

tests: ${LV_TESTS_TARGETS}
clean-tests:
	rm -rf tests/*.objects/

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
