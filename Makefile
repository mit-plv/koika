BUILD_DIR := _build/default
PHONY :=

default: examples

#######
# Coq #
#######

# FIXME: These ‘cp’ calls shouldn't be needed; see
# https://discuss.ocaml.org/t/4462/
coq:
	@rm -f _build/default/coq/Extraction.vo
	dune build coq/Extraction.vo
	cp _build/default/coq/extracted.ml ocaml/cuttlebone/extr.ml
	cp _build/default/coq/extracted.mli ocaml/cuttlebone/extr.mli

coq-all:
	dune build @coq/all

PHONY += coq coq-all

#########
# OCaml #
#########

COQ_DEMO_EXE := ${BUILD_DIR}/ocaml/demo.exe
CUTTLEC_EXE := ${BUILD_DIR}/ocaml/cuttlec.exe

# FIXME: remove the @echo line below once the fix to
# https://github.com/ocaml/dune/issues/138 is released
# FIXME: The coq dependency is because dune doesn't track the dependency on
# Extraction.vo at the moment.
ocaml-executables: coq
	dune build ocaml/demo.exe ocaml/demo.bc ocaml/cuttlec.exe ocaml/cuttlec.bc
	@echo Leaving directory \`$(abspath $(dir $(lastword $(PWD))))\'

# This prevents make from running two instances of Dune in parallel
${COQ_DEMO_EXE} ${CUTTLEC_EXE}: ocaml-executables;

ocaml: ${COQ_DEMO_EXE} ${CUTTLEC_EXE}

PHONY += ocaml ocaml-executables

####################
# Examples & tests #
####################

COOKIE:=_built
LV_EXAMPLES := $(wildcard examples/*.lv)
LV_EXAMPLES_TARGETS := $(patsubst %.lv,%.lv.objects/${COOKIE},${LV_EXAMPLES})
LV_TESTS := $(wildcard tests/*.lv)
LV_TESTS_TARGETS := $(patsubst %.lv,%.lv.objects/${COOKIE},${LV_TESTS})
COQ_DEMO_TARGET := examples/demo.v.objects

# ‘cd ocaml’ because cpp.ml needs to run from one specific directory
%.lv.objects/${COOKIE}: %.lv ${CUTTLEC_EXE}
	mkdir -p "$<.objects"
	cd ocaml/; \
		> "../$<.objects/stderr" \
		../${CUTTLEC_EXE} "../$<" "../$<.objects/$(notdir $*).all" || true
	touch "$<.objects/${COOKIE}"

${COQ_DEMO_TARGET}: ${COQ_DEMO_EXE}
	cd ocaml/; ../${COQ_DEMO_EXE}

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
