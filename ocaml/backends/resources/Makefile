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
CUTTLEC_S_FLAGS ?= -DSIM_MINIMAL -fverbose-asm
CUTTLEC_WARNINGS ?= __CUTTLEC_CXX_WARNINGS__

cuttlesim_helper := cuttlesim.hpp
cxx_flags := $(CXXFLAGS) $(CPPFLAGS) $(CUTTLEC_WARNINGS) __CUTTLEC_CXX_BASE_FLAGS__

$(mod).opt: $(cuttlesim_helper) $(mod).hpp $(CPP_DRIVER)
	$(CXX) $(cxx_flags) $(CUTTLEC_OPT_FLAGS) $(CPP_DRIVER) -o "$@"

$(mod).debug: $(cuttlesim_helper) $(mod).hpp $(CPP_DRIVER)
	$(CXX) $(cxx_flags) $(CUTTLEC_DEBUG_FLAGS) $(CPP_DRIVER) -o "$@"

$(mod).opt.debug: $(mod).hpp $(CPP_DRIVER)
	$(CXX) $(cxx_flags) $(CUTTLEC_OPT_FLAGS) $(CUTTLEC_DEBUG_FLAGS) $(CPP_DRIVER) -o "$@"

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
sim_invoke_opt_debug := ./$(mod).opt.debug $(SIM_ARGS) $(NCYCLES)
sim_invoke_coverage := ./$(mod).cov $(SIM_ARGS) $(NCYCLES)

$(mod).out: $(mod).opt
	time $(sim_invoke_opt) > "$@"

$(mod).cuttlesim.vcd: $(mod).opt
	time $(sim_invoke_opt) "$@"

# Debugging
# =========

GDBFLAGS ?= -tui
GDBOPTS ?= -x "set print array on" -x "set print pretty on"

gdb: $(mod).debug
	gdb $(GDBFLAGS) $(GDBOPTS) --args $(sim_invoke_debug)

LLDBFLAGS ?=

lldb: $(mod).debug
	lldb $(LLDBFLAGS) -- $(sim_invoke_debug)

# Profiling
# =========

$(mod).perf: $(mod).opt.debug
	time perf record -e "cycles:pp" -o "$@" -- $(sim_invoke_opt) || (rm -f "$@"; exit 1)

perf: $(mod).perf
	perf report -i "$<"

$(mod).callgrind: $(mod).opt.debug
	time valgrind --tool=callgrind --callgrind-out-file="$@" $(sim_invoke_opt_debug)

kcachegrind: $(mod).callgrind
	kcachegrind "$<"

GCOV_OPTS ?= --branch-counts --demangled-names --relative-only

$(mod).hpp.gcov $(CPP_DRIVER).gcov: $(mod).gcno $(mod).cov
	time $(sim_invoke_coverage)
	gcov $(GCOV_OPTS) $(CPP_DRIVER)

#############
# Verilator #
#############

verilator_optdir := obj_dir.opt
verilator_tracedir := obj_dir.trace

VERILATOR_TOPLEVEL ?= $(mod).v
VERILATOR_DRIVER ?= $(shell pwd)/$(mod).verilator.cpp
VERILATOR_WARNINGS ?= -Wall -Wno-fatal
VERILATOR_OPT_FLAGS ?= --x-assign fast --x-initial fast --noassert --compiler gcc
VERILATOR_TRACE_FLAGS ?=

vmod := V$(basename $(VERILATOR_TOPLEVEL))
verilator_helper := verilator.hpp
verilator_cflags := -CFLAGS "-I $(shell pwd)"
verilator_std_flags := $(VERILATOR_WARNINGS) $(verilator_cflags) --cc --exe
verilator_inputs := $(VERILATOR_DRIVER) $(VERILATOR_TOPLEVEL)
verilator_deps := $(verilator_helper) $(verilator_inputs) $(wildcard *.sv) $(wildcard *.v)

$(verilator_optdir)/$(vmod).mk: $(verilator_deps)
	verilator $(verilator_std_flags) --Mdir $(verilator_optdir) $(VERILATOR_OPT_FLAGS) $(verilator_inputs)

$(verilator_tracedir)/$(vmod).mk: $(verilator_deps)
	verilator $(verilator_std_flags) --Mdir $(verilator_tracedir) -CFLAGS "-DTRACE" --trace $(VERILATOR_TRACE_FLAGS) $(verilator_inputs)

# $(verilator_deps) because verilator doesn't always update its Makefiles
$(verilator_optdir)/$(vmod): $(verilator_optdir)/$(vmod).mk $(verilator_deps)
	+$(MAKE) OPT="-O3" -C $(verilator_optdir) -f $(vmod).mk $(vmod)

$(verilator_tracedir)/$(vmod): $(verilator_tracedir)/$(vmod).mk $(verilator_deps)
	+$(MAKE) OPT="-g" -C $(verilator_tracedir) -f $(vmod).mk $(vmod)

###################
# Default targets #
###################

clean:
	rm -f $(mod).opt
	rm -f $(mod).debug
	rm -f $(mod).opt.debug
	rm -f $(mod).s
	rm -f $(mod).out
	rm -f $(mod).cuttlesim.vcd
	rm -f $(mod).perf
	rm -f $(mod).callgrind
	rm -fr $(verilator_objdir)

help:
	@echo 'Targets'
	@echo '  Cuttlesim'
	@echo '    Compiling'
	@echo '      $(mod).opt:'
	@echo '        Optimized build'
	@echo '      $(mod).debug:'
	@echo '        Debugger-friendly build'
	@echo '      $(mod).opt.debug:'
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
	@echo '    Debugging'
	@echo '      gdb:'
	@echo '        Run $(mod.debug) under GDB'
	@echo '      lldb:'
	@echo '        Run $(mod.debug) under LLDB'
	@echo '    Profiling'
	@echo '      $(mod).perf:'
	@echo '        ‘perf’ profile of $(mod).opt'
	@echo '      perf:'
	@echo '        Show perf report'
	@echo '      $(mod).callgrind:'
	@echo '        Valgrind trace of $(mod).opt.debug'
	@echo '      kcachegrind:'
	@echo '        Visualize $(mod).callgrind'
	@echo '      $(mod).hpp.gcov:'
	@echo '      $(CPP_DRIVER).gcov:'
	@echo '        Generate coverage statistics (useful to see how often rules fail and why)'
	@echo '  Verilator'
	@echo '    $(verilator_optdir)/$(vmod):'
	@echo '      Optimized Verilator binary'
	@echo '    $(verilator_tracedir)/$(vmod):'
	@echo '      Verilator binary built with --trace'
	@echo ''
	@echo 'Options'
	@echo '  DEFAULT_TARGET = $(DEFAULT_TARGET)'
	@echo '    Makefile target to run by default.'
	@echo '  Cuttlesim'
	@echo '    Compiler settings'
	@echo '      CPPFLAGS = $(CPPFLAGS)'
	@echo '      CXXFLAGS = $(CXXFLAGS)'
	@echo '        C++ compiler flags.'
	@echo '      CPP_DRIVER = $(CPP_DRIVER)'
	@echo '        CPP file driving the cuttlesim simulation.  Can be generated by cuttlec.'
	@echo '      CUTTLEC_OPT_FLAGS = $(CUTTLEC_OPT_FLAGS)'
	@echo '        C++ compiler flags used in opt mode'
	@echo '      CUTTLEC_DEBUG_FLAGS = $(CUTTLEC_DEBUG_FLAGS)'
	@echo '        C++ compiler flags used in debug mode'
	@echo '      CUTTLEC_S_FLAGS = $(CUTTLEC_S_FLAGS)'
	@echo '        C++ compiler flags used to generate assembly listings'
	@echo '      CUTTLEC_WARNINGS = $(CUTTLEC_WARNINGS)'
	@echo '        Additional C++ compiler flags controlling warnings'
	@echo '    Run-time settings'
	@echo '      NCYCLES = $(NCYCLES)'
	@echo '        How many cycles to run the simulation for'
	@echo '      SIM_ARGS = $(SIM_ARGS)'
	@echo '        Command-line arguments passed to the C++ model'
	@echo '      GDBFLAGS = $(GDBFLAGS)'
	@echo '        Command-line arguments passed to GDB'
	@echo '      GDBOPTS = $(GDBOPTS)'
	@echo '        Additional command-line options passed to GDB'
	@echo '      LLDBFLAGS = $(LLDBFLAGS)'
	@echo '        Command-line arguments passed to LLDB'
	@echo '  Verilator'
	@echo '    VERILATOR_TOPLEVEL = $(VERILATOR_TOPLEVEL)'
	@echo '      Verilog or SystemVerilog file wrapping the code compiled by cuttlec.'
	@echo '    VERILATOR_DRIVER = $(VERILATOR_DRIVER)'
	@echo '      C++ file driving the verilator simulation.  Can be generated by cuttlec.'
	@echo '    VERILATOR_OPT_FLAGS = $(VERILATOR_OPT_FLAGS)'
	@echo '      Verilator ags used in opt mode'
	@echo '    VERILATOR_WARNINGS = $(VERILATOR_WARNINGS)'
	@echo '      Additionalerilator flags controlling warnings'
	@echo '    VERILATOR_TRACE_FLAGS = $(VERILATOR_TRACE_FLAGS)'
	@echo '      Verilator ags used in trace mode'

.PHONY: gdb lldb perf kcachegrind clean help
