mod := __CUTTLEC_MODULE_NAME__

all: default_target;

-include Makefile.conf

DEFAULT_TARGET ?= $(mod).opt
default_target: $(DEFAULT_TARGET);

##############
# Simulation #
##############

# Compilation
# ===========

CPPFLAGS ?=
CXXFLAGS ?=
CPP_DRIVER ?= $(mod).cpp
CUTTLEC_OPT_FLAGS ?= __CUTTLEC_CXX_OPT_FLAGS__
CUTTLEC_DEBUG_FLAGS ?= -g
CUTTLEC_PERF_FLAGS ?= -DSIM_NOINLINE $(CUTTLEC_OPT_FLAGS) $(CUTTLEC_DEBUG_FLAGS)
CUTTLEC_S_FLAGS ?= -DSIM_MINIMAL -fverbose-asm
CUTTLEC_WARNINGS ?= __CUTTLEC_CXX_WARNINGS__
VCD_SCOPES ?= TOP $(mod)

comma := ,
cuttlesim_helper := cuttlesim.hpp
cxx_scopes_arg := '-DSIM_VCD_SCOPES={$(patsubst %,"%"$(comma),$(VCD_SCOPES))}'
cxx_flags := $(CXXFLAGS) $(CPPFLAGS) $(CUTTLEC_WARNINGS) $(cxx_scopes_arg)

ifeq (,$(findstring --std,$(cxx_flags)))
cxx_flags += __CUTTLEC_CXX_STANDARD__
endif

$(mod).opt: $(cuttlesim_helper) $(mod).hpp $(CPP_DRIVER)
	$(CXX) $(cxx_flags) $(CUTTLEC_OPT_FLAGS) $(CPP_DRIVER) -o "$@"

$(mod).debug: $(cuttlesim_helper) $(mod).hpp $(CPP_DRIVER)
	$(CXX) $(cxx_flags) $(CUTTLEC_DEBUG_FLAGS) $(CPP_DRIVER) -o "$@"

$(mod).perf: $(mod).hpp $(CPP_DRIVER)
	$(CXX) $(cxx_flags) $(CUTTLEC_PERF_FLAGS) $(CPP_DRIVER) -o "$@"

$(mod).gcno $(mod).cov:
	$(CXX) $(cxx_flags) $(CUTTLEC_DEBUG_FLAGS) --coverage $(CPP_DRIVER) -o "$@"

cxx_s_flags := $(CUTTLEC_S_FLAGS) -fno-asynchronous-unwind-tables -fno-exceptions -fno-rtti -masm=intel -S
$(mod).s: $(mod).hpp $(CPP_DRIVER)
	$(CXX) $(cxx_flags) $(CUTTLEC_OPT_FLAGS) $(cxx_s_flags) $(CPP_DRIVER) -o - | c++filt > "$@"

$(mod).tree $(mod).tree/: $(mod).hpp $(CPP_DRIVER)
	$(CXX) $(cxx_flags) $(CUTTLEC_OPT_FLAGS) $(cxx_s_flags) -fdump-tree-all $(CPP_DRIVER) -o $(mod).tree/$(mod).s

# Tracing
# =======

NCYCLES ?= -1
SIM_ARGS ?=

sim_invoke_opt := ./$(mod).opt $(SIM_ARGS) $(NCYCLES)
sim_invoke_debug := ./$(mod).debug $(SIM_ARGS) $(NCYCLES)
sim_invoke_perf := ./$(mod).perf $(SIM_ARGS) $(NCYCLES)
sim_invoke_coverage := ./$(mod).cov $(SIM_ARGS) $(NCYCLES)

$(mod).out: $(mod).opt
	time $(sim_invoke_opt) > "$@"

$(mod).cuttlesim.vcd: $(mod).opt
	time $(sim_invoke_opt) "$@"

gtkwave.cuttlesim: $(mod).cuttlesim.vcd
	gtkwave $<

# Debugging
# =========

GDB_FLAGS ?= -tui
GDB_OPTS ?= -ex "set print array on" -ex "set print pretty on"

gdb: $(mod).debug
	gdb $(GDB_FLAGS) $(GDB_OPTS) --args $(sim_invoke_debug)

LLDB_FLAGS ?=

lldb: $(mod).debug
	lldb $(LLDB_FLAGS) -- $(sim_invoke_debug)

# Profiling
# =========

$(mod).perf.data: $(mod).perf
	time perf record -e "cycles:pp" -o "$@" -- $(sim_invoke_perf) || (rm -f "$@"; exit 1)

PERF_FLAGS ?= -M intel

perf: $(mod).perf.data
	perf report $(PERF_FLAGS) -i "$<"

$(mod).callgrind: $(mod).perf
	time valgrind --tool=callgrind --callgrind-out-file="$@" $(sim_invoke_perf)

kcachegrind: $(mod).callgrind
	kcachegrind "$<"

GCOV_OPTS ?= --branch-counts --demangled-names --relative-only

$(mod).hpp.gcov $(CPP_DRIVER).gcov: $(mod).gcno $(mod).cov
	time $(sim_invoke_coverage)
	gcov $(GCOV_OPTS) $(CPP_DRIVER)

#############
# Verilator #
#############

# Compilation
# ===========

verilator_optdir := obj_dir
verilator_tracedir := obj_dir.trace

VERILATOR_FLAGS ?=
VERILATOR_TOPLEVEL ?= $(mod).v
VERILATOR_DRIVER ?= $(shell pwd)/$(mod).verilator.cpp
VERILATOR_WARNINGS ?= -Wall -Wno-fatal
VERILATOR_OPT_FLAGS ?= --x-assign fast --x-initial fast --noassert
VERILATOR_TRACE_FLAGS ?=

ifeq ($(CXX),g++)
verilator_compiler_flags := --compiler gcc
else ifeq ($(CXX),clang++)
verilator_compiler_flags := --compiler clang -CFLAGS -fPIC
else
verilator_compiler_flags :=
endif

vmod := V$(basename $(VERILATOR_TOPLEVEL))
verilator_helper := verilator.hpp
verilator_cflags := -CFLAGS "-I $(shell pwd)"
verilator_flags := $(VERILATOR_FLAGS) $(VERILATOR_WARNINGS) $(verilator_cflags) --cc --exe $(verilator_compiler_flags)
verilator_inputs := $(VERILATOR_DRIVER) $(VERILATOR_TOPLEVEL)
verilator_deps := $(verilator_helper) $(verilator_inputs) $(wildcard *.sv) $(wildcard *.v)

$(verilator_optdir)/$(vmod).mk: $(verilator_deps)
	verilator $(verilator_flags) --Mdir $(verilator_optdir) $(VERILATOR_OPT_FLAGS) $(verilator_inputs)

$(verilator_tracedir)/$(vmod).mk: $(verilator_deps)
	verilator $(verilator_flags) --Mdir $(verilator_tracedir) -CFLAGS "-DTRACE" --trace $(VERILATOR_TRACE_FLAGS) $(verilator_inputs)

# $(verilator_deps) because verilator doesn't always update its Makefiles
$(verilator_optdir)/$(vmod): $(verilator_optdir)/$(vmod).mk $(verilator_deps)
	+$(MAKE) OPT="-O3" -C $(verilator_optdir) -f $(vmod).mk $(vmod)

$(verilator_tracedir)/$(vmod): $(verilator_tracedir)/$(vmod).mk $(verilator_deps)
	+$(MAKE) OPT="-g" -C $(verilator_tracedir) -f $(vmod).mk $(vmod)

$(verilator_optdir)/$(vmod).xml: $(verilator_deps)
	verilator $(VERILATOR_WARNINGS) $(VERILATOR_TOPLEVEL) --Mdir $(verilator_optdir) -xml-only --bbox-sys

# Tracing
# =======

VERILATOR_ARGS ?=

verilator_invoke_trace := ./$(verilator_tracedir)/$(vmod) $(VERILATOR_ARGS) $(NCYCLES)

$(mod).verilator.vcd: $(verilator_tracedir)/$(vmod)
	time $(verilator_invoke_trace) "$@"

ifeq (, $(shell which xml2stems))
$(warning xml2stems not found: not showing rtlbrowse; try installing a more recent version of GTKWave.)
gtkwave.verilator: $(mod).verilator.vcd
	gtkwave --optimize $<
else
# Use xml2stems because Vermin only parses up to Verilog 1995 and we use [+:] from Verilog 2000
$(VERILATOR_TOPLEVEL).stems: $(verilator_optdir)/$(vmod).xml
	xml2stems $< $@

gtkwave.verilator: $(VERILATOR_TOPLEVEL).stems $(mod).verilator.vcd
	gtkwave --optimize --stems $^
endif

twinwave: $(mod).cuttlesim.vcd $(mod).verilator.vcd
	twinwave $(mod).cuttlesim.vcd + $(mod).verilator.vcd

###################
# Default targets #
###################

clean:
	rm -f $(mod).opt
	rm -f $(mod).debug
	rm -f $(mod).perf
	rm -f $(mod).cov
	rm -f $(mod).s
	rm -f $(mod).out
	rm -f $(mod).cuttlesim.vcd
	rm -f $(mod).perf.data
	rm -f $(mod).callgrind
	rm -f *.gcov
	rm -fr $(verilator_optdir)
	rm -fr $(verilator_tracedir)
	rm -f $(mod).verilator.vcd

help:
	@echo 'Targets'
	@echo '  Cuttlesim'
	@echo '    Compiling'
	@echo '      $(mod).opt:'
	@echo '        Optimized build'
	@echo '      $(mod).debug:'
	@echo '        Debugger-friendly build'
	@echo '      $(mod).perf:'
	@echo '        Profiler-friendly build'
	@echo '      $(mod).cov:'
	@echo '        Coverage-instrumented build'
	@echo '      $(mod).s:'
	@echo '        Assembly dump in SIM_MINIMAL mode'
	@echo '      $(mod).tree/:'
	@echo '        Dump of GCC’s optimization passes'
	@echo '    Tracing'
	@echo '      $(mod).out:'
	@echo '        Output produced by $(mod).opt'
	@echo '      $(mod).cuttlesim.vcd:'
	@echo '        VCD trace of $(mod).opt'
	@echo '      gtkwave.cuttlesim:'
	@echo '        View $(mod).cuttlesim.vcd'
	@echo '    Debugging'
	@echo '      gdb:'
	@echo '        Run $(mod.debug) under GDB'
	@echo '      lldb:'
	@echo '        Run $(mod.debug) under LLDB'
	@echo '    Profiling'
	@echo '      $(mod).perf.data:'
	@echo '        ‘perf’ profile of $(mod).perf'
	@echo '      perf:'
	@echo '        Show perf report'
	@echo '      $(mod).callgrind:'
	@echo '        Valgrind trace of $(mod).perf'
	@echo '      kcachegrind:'
	@echo '        Visualize $(mod).callgrind'
	@echo '      $(mod).hpp.gcov:'
	@echo '      $(CPP_DRIVER).gcov:'
	@echo '        Generate coverage statistics (useful to see how often rules fail and why)'
	@echo '  Verilator'
	@echo '    Compiling'
	@echo '      $(verilator_optdir)/$(vmod):'
	@echo '        Optimized Verilator binary'
	@echo '      $(verilator_tracedir)/$(vmod):'
	@echo '        Verilator binary built with --trace'
	@echo '    Tracing'
	@echo '      $(mod).verilator.vcd:'
	@echo '        VCD trace of $(verilator_tracedir)/$(vmod)'
	@echo '      gtkwave.verilator:'
	@echo '        View $(mod).verilator.vcd'
	@echo '      twinwave:'
	@echo '        Compare the traces generated by Verilator and Cuttlesim'
	@echo ''
	@echo 'Options'
	@echo '  DEFAULT_TARGET = $(DEFAULT_TARGET)'
	@echo '    Makefile target to run by default.'
	@echo '  Cuttlesim'
	@echo '    Compiler settings'
	@echo '      CPPFLAGS = $(CPPFLAGS)'
	@echo '      CXXFLAGS = $(CXXFLAGS)'
	@echo '        Additional C++ compiler flags.'
	@echo '      CPP_DRIVER = $(CPP_DRIVER)'
	@echo '        CPP file driving the cuttlesim simulation.  Can be generated by cuttlec.'
	@echo '      CUTTLEC_OPT_FLAGS = $(CUTTLEC_OPT_FLAGS)'
	@echo '        C++ compiler flags used in opt mode'
	@echo '      CUTTLEC_DEBUG_FLAGS = $(CUTTLEC_DEBUG_FLAGS)'
	@echo '        C++ compiler flags used in debug mode'
	@echo '      CUTTLEC_DEBUG_FLAGS = $(CUTTLEC_DEBUG_FLAGS)'
	@echo '        C++ compiler flags used in perf mode'
	@echo '      CUTTLEC_S_FLAGS = $(CUTTLEC_S_FLAGS)'
	@echo '        C++ compiler flags used to generate assembly listings'
	@echo '      CUTTLEC_WARNINGS = $(CUTTLEC_WARNINGS)'
	@echo '        Additional C++ compiler flags controlling warnings'
	@echo '      VCD_SCOPES = $(VCD_SCOPES)'
	@echo '        Module hierarchy (space-separated, unquoted) to use in Cuttlesim\'s VCD files'
	@echo '    Run-time settings'
	@echo '      NCYCLES = $(NCYCLES)'
	@echo '        How many cycles to run the simulation for'
	@echo '      SIM_ARGS = $(SIM_ARGS)'
	@echo '        Command-line arguments passed to the Cuttlesim model'
	@echo '      GDB_FLAGS = $(GDB_FLAGS)'
	@echo '        Command-line arguments passed to GDB'
	@echo '      GDB_OPTS = $(GDB_OPTS)'
	@echo '        Additional command-line options passed to GDB'
	@echo '      LLDB_FLAGS = $(LLDB_FLAGS)'
	@echo '        Command-line arguments passed to LLDB'
	@echo '      PERF_FLAGS = $(PERF_FLAGS)'
	@echo '        Command-line arguments passed to perf'
	@echo '  Verilator'
	@echo '    Compiler settings'
	@echo '      VERILATOR_TOPLEVEL = $(VERILATOR_TOPLEVEL)'
	@echo '        Verilog or SystemVerilog file wrapping the code compiled by cuttlec.'
	@echo '      VERILATOR_DRIVER = $(VERILATOR_DRIVER)'
	@echo '        C++ file driving the verilator simulation.  Can be generated by cuttlec.'
	@echo '      VERILATOR_FLAGS = $(VERILATOR_FLAGS)'
	@echo '        Additional Verilator flags'
	@echo '      VERILATOR_WARNINGS = $(VERILATOR_WARNINGS)'
	@echo '        Verilator flags controlling warnings'
	@echo '      VERILATOR_OPT_FLAGS = $(VERILATOR_OPT_FLAGS)'
	@echo '        Verilator flags used in opt mode'
	@echo '      VERILATOR_TRACE_FLAGS = $(VERILATOR_TRACE_FLAGS)'
	@echo '        Verilator flags used in trace mode'
	@echo '    Run-time settings'
	@echo '      VERILATOR_ARGS = $(VERILATOR_ARGS)'
	@echo '        Command-line arguments passed to the Verilator model'
	@echo '      NCYCLES = $(NCYCLES)'
	@echo '        How many cycles to run the simulation for'

.PHONY: gdb lldb perf kcachegrind gtkwave.cuttlesim gtkwave.verilator twinwave clean help
