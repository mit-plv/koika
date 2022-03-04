################################################
#            Check makefile version            #
# (https://github.com/mit-plv/koika/issues/18) #
################################################

ifeq ($(filter output-sync,$(value .FEATURES)),)
$(info You have Make version $(MAKE_VERSION).)
$(error Unsupported version of Make. Please use GNU Make >= 4.0)
endif

####################
# Global variables #
####################

OBJ_DIR := _obj
BUILD_DIR := _build/default
COQ_BUILD_DIR := ${BUILD_DIR}/coq
OCAML_BUILD_DIR := ${BUILD_DIR}/ocaml

V ?=
verbose := $(if $(V),,@)

default: all

#######
# Coq #
#######

coq:
	@printf "\n== Building Coq library ==\n"
	dune build @@coq/all

coq-all:
	@printf "\n== Building Coq library and proofs ==\n"
	dune build @coq/all

CHECKED_MODULES ?= OneRuleAtATime CompilerCorrectness/Correctness
checked_paths := $(patsubst %,$(COQ_BUILD_DIR)/%.vo,$(CHECKED_MODULES))

coq-check: coq-all
	coqchk --output-context -R $(COQ_BUILD_DIR) Koika $(checked_paths)

.PHONY: coq coq-all coq-check

#########
# OCaml #
#########

ocaml:
	@printf "\n== Building OCaml library and executables ==\n"
	dune build ocaml/cuttlec.exe @install

.PHONY: ocaml

####################
# Examples & tests #
####################

# The setup below generates one Makefile rule per target.  It uses canned rules
# and eval because patterns like ‘%1/_objects/%2.v/: %1/%2.v’ aren't supported.
# https://www.gnu.org/software/make/manual/html_node/Canned-Recipes.html
# https://www.gnu.org/software/make/manual/html_node/Eval-Function.html

target_directory = $(dir $(1))_objects/$(notdir $(1))
target_directories = $(foreach fname,$(1),$(call target_directory,$(fname)))

define cuttlec_recipe_prelude =
	@printf "\n-- Compiling %s --\n" "$<"
endef

# Execute follow-ups if any
define cuttlec_recipe_coda =
	$(verbose)if [ -d $<.etc ]; then cp -rf $<.etc/. "$@"; fi
	$(verbose)if [ -d $(dir $<)etc ]; then cp -rf $(dir $<)etc/. "$@"; fi
	$(verbose)if [ -f "$@/Makefile" ]; then $(MAKE) -C "$@"; fi
endef

# Compile a .lv file
define cuttlec_lv_recipe_body =
	dune exec -- cuttlec "$<" \
		-T all -o "$@" $(if $(findstring .1.,$<),--expect-errors 2> "$@stderr")
endef

# Compile a .v file
define cuttlec_v_recipe_body =
	dune build "$@/$(notdir $(<:.v=.ml))"
	dune exec -- cuttlec "${BUILD_DIR}/$@/$(notdir $(<:.v=.ml))" -T all -o "$@"
endef

define cuttlec_lv_template =
$(eval dirpath := $(call target_directory,$(1)))
$(dirpath) $(dirpath)/: $(1) ocaml | configure
	$(value cuttlec_recipe_prelude)
	$(value cuttlec_lv_recipe_body)
	$(value cuttlec_recipe_coda)
endef

define cuttlec_v_template =
$(eval dirpath := $(call target_directory,$(1)))
$(dirpath) $(dirpath)/: $(1) ocaml | configure
	$(value cuttlec_recipe_prelude)
	$(value cuttlec_v_recipe_body)
	$(value cuttlec_recipe_coda)
endef

TESTS := $(wildcard tests/*.lv) $(wildcard tests/*.v)
EXAMPLES := $(wildcard examples/*.lv) $(wildcard examples/*.v) examples/rv/rv32i.v examples/rv/rv32e.v

configure:
	etc/configure $(filter %.v,${TESTS} ${EXAMPLES})

$(foreach fname,$(filter %.lv, $(EXAMPLES) $(TESTS)),\
	$(eval $(call cuttlec_lv_template,$(fname))))
$(foreach fname,$(filter %.v, $(EXAMPLES) $(TESTS)),\
	$(eval $(call cuttlec_v_template,$(fname))))

examples: $(call target_directories,$(EXAMPLES));
clean-examples:
	find examples/ -type d \( -name _objects -or -name _build \) -exec rm -rf {} +
	rm -rf ${BUILD_DIR}/examples

tests: $(call target_directories,$(TESTS));
clean-tests:
	find tests/ -type d  \( -name _objects -or -name _build \) -exec rm -rf {} +
	rm -rf ${BUILD_DIR}/tests

.PHONY: configure examples clean-examples tests clean-tests

#################
# Whole project #
#################

readme:
	./etc/readme/update.py README.rst

package:
	etc/package.sh

dune-all: coq ocaml
	@printf "\n== Completing full build ==\n"
	dune build @all

all: coq ocaml examples tests readme;

clean: clean-tests clean-examples
	dune clean
	rm -f koika-*.tar.gz

.PHONY: readme package dune-all all clean

.SUFFIXES:

# Running two copies of dune in parallel isn't safe, and dune is already
# handling most of the parallelism for us
.NOTPARALLEL:

# Disable built-in rules
MAKEFLAGS += --no-builtin-rules
.SUFFIXES:
