mod := __CUTTLEC_MODULE_NAME__

.DEFAULT_GOAL := default
-include Makefile.conf

#############
# Cuttlesim #
#############

# Compilation
# ===========

CPPFLAGS ?=
CXXFLAGS ?=
CUTTLESIM_DRIVER ?= $(mod).cpp
CUTTLESIM_OPT_FLAGS ?= __CUTTLEC_CXX_OPT_FLAGS__
CUTTLESIM_DEBUG_FLAGS ?= -Og -ggdb3
CUTTLESIM_PERF_FLAGS ?= -DSIM_NOINLINE $(CUTTLESIM_OPT_FLAGS) $(CUTTLESIM_DEBUG_FLAGS)
CUTTLESIM_COV_FLAGS ?= $(CUTTLESIM_DEBUG_FLAGS)
CUTTLESIM_S_FLAGS ?= -DSIM_MINIMAL -fverbose-asm
CUTTLESIM_WARNINGS ?= __CUTTLEC_CXX_WARNINGS__
CUTTLESIM_VCD_SCOPES ?= TOP $(mod)

comma := ,
cuttlesim_driver := $(basename $(CUTTLESIM_DRIVER))
cuttlesim_helper := cuttlesim.hpp
cxx_scopes_arg := '-DSIM_CUTTLESIM_VCD_SCOPES={$(patsubst %,"%"$(comma),$(CUTTLESIM_VCD_SCOPES))}'
cxx_flags := $(CXXFLAGS) $(CPPFLAGS) $(CUTTLESIM_WARNINGS) $(cxx_scopes_arg)

ifeq (,$(findstring --std,$(cxx_flags)))
cxx_flags += __CUTTLEC_CXX_STANDARD__
endif

ifdef CUTTLESIM_DEBUG_SANITIZE
export LSAN_OPTIONS ?= verbosity=1
export UBSAN_OPTIONS ?= print_stacktrace=1
cuttlec_debug_flags += -fsanitize=address,undefined -fsanitize-recover=all
endif

$(cuttlesim_driver).opt: $(cuttlesim_helper) $(mod).hpp $(CUTTLESIM_DRIVER)
	$(CXX) $(cxx_flags) $(CUTTLESIM_OPT_FLAGS) $(CUTTLESIM_DRIVER) -o "$@"

$(cuttlesim_driver).debug: $(cuttlesim_helper) $(mod).hpp $(CUTTLESIM_DRIVER)
	$(CXX) $(cxx_flags) $(CUTTLESIM_DEBUG_FLAGS) $(CUTTLESIM_DRIVER) -o "$@"

$(cuttlesim_driver).perf: $(mod).hpp $(CUTTLESIM_DRIVER)
	$(CXX) $(cxx_flags) $(CUTTLESIM_PERF_FLAGS) $(CUTTLESIM_DRIVER) -o "$@"

$(cuttlesim_driver).gcno $(cuttlesim_driver).cov: $(mod).hpp $(CUTTLESIM_DRIVER)
	$(CXX) $(cxx_flags) $(CUTTLESIM_COV_FLAGS) --coverage $(CUTTLESIM_DRIVER) -o "$@"

cxx_s_flags := $(CUTTLESIM_S_FLAGS) -fno-asynchronous-unwind-tables -fno-exceptions -fno-rtti -masm=intel -S
$(cuttlesim_driver).s: $(mod).hpp $(CUTTLESIM_DRIVER)
	$(CXX) $(cxx_flags) $(CUTTLESIM_OPT_FLAGS) $(cxx_s_flags) $(CUTTLESIM_DRIVER) -o - | c++filt > "$@"

$(cuttlesim_driver).tree $(cuttlesim_driver).tree/: $(mod).hpp $(CUTTLESIM_DRIVER)
	$(CXX) $(cxx_flags) $(CUTTLESIM_OPT_FLAGS) $(cxx_s_flags) -fdump-tree-all $(CUTTLESIM_DRIVER) -o $(cuttlesim_driver).tree/$(cuttlesim_driver).s

# Tracing
# =======

NCYCLES ?= -1
CUTTLESIM_ARGS ?=

sim_invoke_opt := ./$(cuttlesim_driver).opt $(CUTTLESIM_ARGS) $(NCYCLES)
sim_invoke_debug := ./$(cuttlesim_driver).debug $(CUTTLESIM_ARGS) $(NCYCLES)
sim_invoke_perf := ./$(cuttlesim_driver).perf $(CUTTLESIM_ARGS) $(NCYCLES)
sim_invoke_coverage := ./$(cuttlesim_driver).cov $(CUTTLESIM_ARGS) $(NCYCLES)

$(cuttlesim_driver).out: $(cuttlesim_driver).opt
	time $(sim_invoke_opt) > "$@"

$(cuttlesim_driver).vcd: $(cuttlesim_driver).opt
	time $(sim_invoke_opt) "$@"

gtkwave.cuttlesim: $(cuttlesim_driver).vcd
	gtkwave $<

.PHONY: gtkwave.cuttlesim

# Debugging
# =========

GDB_FLAGS ?= -tui
GDB_OPTS ?= -ex "set print array on" -ex "set print pretty on"

gdb: $(cuttlesim_driver).debug
	gdb -quiet $(GDB_FLAGS) $(GDB_OPTS) --args $(sim_invoke_debug)

LLDB_FLAGS ?=

lldb: $(cuttlesim_driver).debug
	lldb $(LLDB_FLAGS) -- $(sim_invoke_debug)

.PHONY: gdb lldb

# Profiling
# =========

$(cuttlesim_driver).perf.data: $(cuttlesim_driver).perf
	time perf record -e "cycles:pp" -o "$@" -- $(sim_invoke_perf) || (rm -f "$@"; exit 1)

PERF_FLAGS ?= -M intel

perf: $(cuttlesim_driver).perf.data
	perf report $(PERF_FLAGS) -i "$<"

$(cuttlesim_driver).callgrind: $(cuttlesim_driver).perf
	time valgrind --tool=callgrind --callgrind-out-file="$@" $(sim_invoke_perf)

kcachegrind: $(cuttlesim_driver).callgrind
	kcachegrind "$<"

GCOV_OPTS ?= --branch-counts --demangled-names --relative-only

$(mod).hpp.gcov $(CUTTLESIM_DRIVER).gcov: $(cuttlesim_driver).gcno $(cuttlesim_driver).cov
	time $(sim_invoke_coverage)
	gcov $(GCOV_OPTS) $(CUTTLESIM_DRIVER)

.PHONY: perf kcachegrind

# Cleanup
# =======

clean-cuttlesim:
	rm -f $(cuttlesim_driver).opt
	rm -f $(cuttlesim_driver).debug
	rm -f $(cuttlesim_driver).perf
	rm -f $(cuttlesim_driver).cov
	rm -f $(cuttlesim_driver).s
	rm -f $(cuttlesim_driver).out
	rm -f $(cuttlesim_driver).vcd
	rm -f $(cuttlesim_driver).perf.data
	rm -f $(cuttlesim_driver).callgrind
	rm -f *.gcov

#############
# Verilator #
#############

# Compilation
# ===========

verilator_optdir := obj_dir.opt
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

verilator_toplevel := $(basename $(VERILATOR_TOPLEVEL))
verilator_driver := $(basename $(VERILATOR_DRIVER))
verilator_prefix := V$(verilator_toplevel)
verilator_helper := verilator.hpp
verilator_cflags := -CFLAGS "-I $(shell pwd)"
verilator_prefix_flag := --prefix $(verilator_prefix)
verilator_flags := $(VERILATOR_FLAGS) $(VERILATOR_WARNINGS) $(verilator_cflags) $(verilator_prefix_flag) --cc --exe $(verilator_compiler_flags)
verilator_inputs := $(VERILATOR_DRIVER) $(VERILATOR_TOPLEVEL)
verilator_deps := $(verilator_helper) $(verilator_inputs) $(wildcard *.sv) $(wildcard *.v)

$(verilator_optdir)/$(verilator_prefix).mk: $(verilator_deps)
	verilator $(verilator_flags) --Mdir $(verilator_optdir) $(VERILATOR_OPT_FLAGS) $(verilator_inputs)

$(verilator_tracedir)/$(verilator_prefix).mk: $(verilator_deps)
	verilator $(verilator_flags) --Mdir $(verilator_tracedir) -CFLAGS "-DTRACE" --trace $(VERILATOR_TRACE_FLAGS) $(verilator_inputs)

# $(verilator_deps) because verilator doesn't always update its Makefiles
$(verilator_optdir)/$(verilator_prefix): $(verilator_optdir)/$(verilator_prefix).mk $(verilator_deps)
	+$(MAKE) OPT="-O3" -C $(verilator_optdir) -f $(verilator_prefix).mk $(verilator_prefix)

$(verilator_tracedir)/$(verilator_prefix): $(verilator_tracedir)/$(verilator_prefix).mk $(verilator_deps)
	+$(MAKE) OPT="-g" -C $(verilator_tracedir) -f $(verilator_prefix).mk $(verilator_prefix)

$(verilator_optdir)/$(verilator_prefix).xml: $(verilator_deps)
	verilator $(VERILATOR_WARNINGS) $(verilator_prefix_flag) -xml-only --bbox-sys --Mdir $(verilator_optdir) $(VERILATOR_TOPLEVEL)

# Tracing
# =======

VERILATOR_ARGS ?=

verilator_invoke_trace := ./$(verilator_tracedir)/$(verilator_prefix) $(VERILATOR_ARGS) $(NCYCLES)

$(verilator_driver).vcd: $(verilator_tracedir)/$(verilator_prefix)
	time $(verilator_invoke_trace) "$@"

ifeq (, $(shell which xml2stems))
gtkwave.verilator: $(verilator_driver).vcd
	echo "Warning: xml2stems not found: not showing rtlbrowse; try installing a more recent version of GTKWave."
	gtkwave -A --optimize $<
else
# Use xml2stems because Vermin only parses up to Verilog 1995 and we use [+:] from Verilog 2000
$(verilator_optdir)/$(verilator_prefix).stems: $(verilator_optdir)/$(verilator_prefix).xml
	xml2stems $< $@

gtkwave.verilator: $(verilator_optdir)/$(verilator_prefix).stems $(verilator_driver).vcd
	gtkwave -A --optimize --stems $^
endif

twinwave: $(cuttlesim_driver).vcd $(verilator_driver).vcd
	twinwave -A $(cuttlesim_driver).vcd + -A $(verilator_driver).vcd

.PHONY: gtkwave.verilator twinwave

# Cleanup
# =======

clean-verilator:
	rm -rf $(verilator_optdir)
	rm -rf $(verilator_tracedir)
	rm -f $(verilator_driver).vcd

##################
# FPGA Synthesis #
##################

FPGA_TOPLEVEL ?= $(mod).v
FPGA_DEVICE ?= lp8k
FPGA_ARACHNE_DEVICE ?=
FPGA_ARACHNE_PACKAGE ?= cm81
FPGA_ARACHNE_PCF ?= pins.pcf

fpga_arachne_device :=
ifneq (, $(FPGA_ARACHNE_DEVICE))
fpga_arachne_device := $(FPGA_ARACHNE_DEVICE)
else ifeq ($(FPGA_DEVICE), lp384)
fpga_arachne_device := 384
else ifeq ($(FPGA_DEVICE), lp1k)
fpga_arachne_device := 1k
else ifeq ($(FPGA_DEVICE), hx1k)
fpga_arachne_device := 1k
else ifeq ($(FPGA_DEVICE), up5k)
fpga_arachne_device := 5k
else ifeq ($(FPGA_DEVICE), lp8k)
fpga_arachne_device := 8k
else ifeq ($(FPGA_DEVICE), hx8k)
fpga_arachne_device := 8k
else
$(error "Unrecognized FPGA_DEVICE `$(FPGA_DEVICE)', please set FPGA_ARACHNE_DEVICE.")
endif

fpga_toplevel := $(basename $(FPGA_TOPLEVEL))

$(fpga_toplevel).blif: $(FPGA_TOPLEVEL)
	yosys -p 'read_verilog $(FPGA_TOPLEVEL); hierarchy -libdir . -top $(fpga_toplevel); synth_ice40 -top $(fpga_toplevel) -blif $@'

$(fpga_toplevel).asc: $(FPGA_ARACHNE_PCF) $(fpga_toplevel).blif
	arachne-pnr --device $(fpga_arachne_device) --package $(FPGA_ARACHNE_PACKAGE) --pcf-file $(FPGA_ARACHNE_PCF) -o $@ -p $^

$(fpga_toplevel).bin: $(fpga_toplevel).asc
	icepack $< $@

$(fpga_toplevel).rpt: $(fpga_toplevel).asc
	icetime -d $(FPGA_DEVICE) -mtr $@ $<

$(fpga_toplevel).blif.v: $(fpga_toplevel).blif
	yosys -p 'read_blif -wideports $^; write_verilog $@'

clean-fpga:
	rm -f $(fpga_toplevel).blif
	rm -f $(fpga_toplevel).asc
	rm -f $(fpga_toplevel).bin
	rm -f $(fpga_toplevel).rpt
	rm -f $(fpga_toplevel).blif.v

###################
# Default targets #
###################

DEFAULT_TARGET ?= $(cuttlesim_driver).opt
default: $(DEFAULT_TARGET)

clean: clean-verilator clean-cuttlesim clean-fpga;

help:
	@echo 'Targets'
	@echo '  Cuttlesim'
	@echo '    Compiling'
	@echo '      $(cuttlesim_driver).opt:'
	@echo '        Optimized build'
	@echo '      $(cuttlesim_driver).debug:'
	@echo '        Debugger-friendly build'
	@echo '      $(cuttlesim_driver).perf:'
	@echo '        Profiler-friendly build'
	@echo '      $(cuttlesim_driver).cov:'
	@echo '        Coverage-instrumented build'
	@echo '      $(cuttlesim_driver).s:'
	@echo '        Assembly dump in SIM_MINIMAL mode'
	@echo '      $(cuttlesim_driver).tree/:'
	@echo '        Dump of GCC’s optimization passes'
	@echo '    Tracing'
	@echo '      $(cuttlesim_driver).out:'
	@echo '        Output produced by $(cuttlesim_driver).opt'
	@echo '      $(cuttlesim_driver).vcd:'
	@echo '        VCD trace of $(cuttlesim_driver).opt'
	@echo '      gtkwave.cuttlesim:'
	@echo '        View $(cuttlesim_driver).vcd'
	@echo '    Debugging'
	@echo '      gdb:'
	@echo '        Run $(cuttlesim_driver).debug under GDB'
	@echo '      lldb:'
	@echo '        Run $(cuttlesim_driver).debug under LLDB'
	@echo '    Profiling'
	@echo '      $(cuttlesim_driver).perf.data:'
	@echo '        ‘perf’ profile of $(cuttlesim_driver).perf'
	@echo '      perf:'
	@echo '        Show perf report'
	@echo '      $(cuttlesim_driver).callgrind:'
	@echo '        Valgrind trace of $(cuttlesim_driver).perf'
	@echo '      kcachegrind:'
	@echo '        Visualize $(cuttlesim_driver).callgrind'
	@echo '      $(mod).hpp.gcov:'
	@echo '      $(CUTTLESIM_DRIVER).gcov:'
	@echo '        Generate coverage statistics (useful to see how often rules fail and why)'
	@echo '  Verilator'
	@echo '    Compiling'
	@echo '      $(verilator_optdir)/$(verilator_prefix):'
	@echo '        Optimized Verilator binary'
	@echo '      $(verilator_tracedir)/$(verilator_prefix):'
	@echo '        Verilator binary built with --trace'
	@echo '    Tracing'
	@echo '      $(verilator_driver).vcd:'
	@echo '        VCD trace of $(verilator_tracedir)/$(verilator_prefix)'
	@echo '      gtkwave.verilator:'
	@echo '        View $(verilator_driver).vcd'
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
	@echo '      CUTTLESIM_DRIVER = $(CUTTLESIM_DRIVER)'
	@echo '        CPP file driving the cuttlesim simulation.  Can be generated by cuttlec.'
	@echo '      CUTTLESIM_OPT_FLAGS = $(CUTTLESIM_OPT_FLAGS)'
	@echo '        C++ compiler flags used in opt mode'
	@echo '      CUTTLESIM_DEBUG_FLAGS = $(CUTTLESIM_DEBUG_FLAGS)'
	@echo '        C++ compiler flags used in debug mode'
	@echo '      CUTTLESIM_PERF_FLAGS = $(CUTTLESIM_PERF_FLAGS)'
	@echo '        C++ compiler flags used in perf mode'
	@echo '      CUTTLESIM_COV_FLAGS = $(CUTTLESIM_COV_FLAGS)'
	@echo '        C++ compiler flags used in coverage mode'
	@echo '      CUTTLESIM_S_FLAGS = $(CUTTLESIM_S_FLAGS)'
	@echo '        C++ compiler flags used to generate assembly listings'
	@echo '      CUTTLESIM_WARNINGS = $(CUTTLESIM_WARNINGS)'
	@echo '        Additional C++ compiler flags controlling warnings'
	@echo '      CUTTLESIM_VCD_SCOPES = $(CUTTLESIM_VCD_SCOPES)'
	@echo '        Module hierarchy (space-separated, unquoted) to use in Cuttlesim'"'"'s VCD files'
	@echo '    Run-time settings'
	@echo '      NCYCLES = $(NCYCLES)'
	@echo '        How many cycles to run the simulation for'
	@echo '      CUTTLESIM_ARGS = $(CUTTLESIM_ARGS)'
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
	@echo '      NCYCLES = $(NCYCLES)'
	@echo '        How many cycles to run the simulation for'
	@echo '      VERILATOR_ARGS = $(VERILATOR_ARGS)'
	@echo '        Command-line arguments passed to the Verilator model'
	@echo '  FPGA Synthesis (IceStorm)'
	@echo '    Compiler settings'
	@echo '      FPGA_TOPLEVEL = $(FPGA_TOPLEVEL)'
	@echo '        Verilog or SystemVerilog file wrapping the code compiled by cuttlec.'
	@echo '      FPGA_DEVICE = $(FPGA_DEVICE)'
	@echo '        Device name passed to icetime.'
	@echo '      FPGA_ARACHNE_DEVICE = $(FPGA_ARACHNE_DEVICE)'
	@echo '        Device name passed to arachne-pnr (inferred from FPGA_DEVICE)'
	@echo '      FPGA_ARACHNE_PACKAGE = $(FPGA_ARACHNE_PACKAGE)'
	@echo '        Package name passed to arachne-pnr'
	@echo '      FPGA_ARACHNE_PCF = $(FPGA_ARACHNE_PCF)'
	@echo '        Physical contraints file passed to arachne-pnr'

.PHONY: default clean-cuttlesim clean-verilog clean-fpga clean help
