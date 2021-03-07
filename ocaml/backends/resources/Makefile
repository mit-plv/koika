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
CUTTLESIM_TRACE_FLAGS ?= -DSIM_TRACE $(CUTTLESIM_OPT_FLAGS)
CUTTLESIM_DEBUG_FLAGS ?= -O0 -ggdb3
CUTTLESIM_PERF_FLAGS ?= $(CUTTLESIM_OPT_FLAGS) -ggdb3
CUTTLESIM_COV_FLAGS ?= $(CUTTLESIM_DEBUG_FLAGS)
CUTTLESIM_S_FLAGS ?= -DSIM_MINIMAL -fverbose-asm
CUTTLESIM_WARNINGS ?= __CUTTLEC_CXX_WARNINGS__
CUTTLESIM_VCD_SCOPES ?= TOP $(mod)

comma := ,
cuttlesim_driver := $(basename $(notdir $(CUTTLESIM_DRIVER)))
cuttlesim_helper := cuttlesim.hpp
cxx_scopes_arg := '-DSIM_VCD_SCOPES={$(patsubst %,"%"$(comma),$(CUTTLESIM_VCD_SCOPES))}'
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

$(cuttlesim_driver).trace.opt: $(cuttlesim_helper) $(mod).hpp $(CUTTLESIM_DRIVER)
	$(CXX) $(cxx_flags) $(CUTTLESIM_TRACE_FLAGS) $(CUTTLESIM_DRIVER) -o "$@"

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

sim_invoke = ./$(cuttlesim_driver).$(1) $(CUTTLESIM_ARGS) $(NCYCLES)

$(cuttlesim_driver).run: $(cuttlesim_driver).opt
	time $(call sim_invoke,opt)

$(cuttlesim_driver).out: $(cuttlesim_driver).opt
	time $(call sim_invoke,opt) > "$@"

$(cuttlesim_driver).vcd: $(cuttlesim_driver).trace.opt
	time $(call sim_invoke,trace.opt) "$@"

$(cuttlesim_driver).gtkwave: $(cuttlesim_driver).vcd
	gtkwave $<

.PHONY: $(cuttlesim_driver).run $(cuttlesim_driver).gtkwave

# Debugging
# =========

GDB_FLAGS ?= -tui
GDB_OPTS ?= -ex "set print array on" -ex "set print pretty on"

gdb: $(cuttlesim_driver).debug
	gdb -quiet $(GDB_FLAGS) $(GDB_OPTS) --args $(call sim_invoke,debug)

LLDB_FLAGS ?=

lldb: $(cuttlesim_driver).debug
	lldb $(LLDB_FLAGS) -- $(call sim_invoke,debug)

RR_RECORD_FLAGS ?=
RR_REPLAY_FLAGS ?=

$(cuttlesim_driver).rr $(cuttlesim_driver).rr/: $(cuttlesim_driver).debug
	rm -fr "$@"
	rr record --output-trace-dir "$@" $(RR_RECORD_FLAGS) -- $(cuttlesim_driver).debug $(sim_args)

rr: $(cuttlesim_driver).rr/
	rr replay $(RR_REPLAY_FLAGS) "$<"

.PHONY: gdb lldb rr

# Profiling
# =========

$(cuttlesim_driver).perf.data: $(cuttlesim_driver).perf
	time perf record -e "cycles:pp" -o "$@" -- $(call sim_invoke,perf) || (rm -f "$@"; exit 1)

PERF_FLAGS ?= -M intel

perf: $(cuttlesim_driver).perf.data
	perf report $(PERF_FLAGS) -i "$<"

$(cuttlesim_driver).callgrind: $(cuttlesim_driver).perf
	time valgrind --tool=callgrind --callgrind-out-file="$@" $(call sim_invoke,perf)

kcachegrind: $(cuttlesim_driver).callgrind
	kcachegrind "$<"

GCOV_OPTS ?= --branch-counts --demangled-names --relative-only

$(mod).hpp.gcov $(CUTTLESIM_DRIVER).gcov: $(cuttlesim_driver).gcno $(cuttlesim_driver).cov
	time $(call sim_invoke,cov)
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
	rm -fr $(cuttlesim_driver).rr
	rm -f *.gcov

#############
# Verilator #
#############

# Compilation
# ===========

verilator_optdir := obj_dir.opt
verilator_tracedir := obj_dir.trace

VERILATOR_FLAGS ?=
VERILATOR_TOP ?= $(mod).v
VERILATOR_DRIVER ?= $(shell pwd)/$(mod).verilator.cpp
VERILATOR_WARNINGS ?= -Wall -Wno-fatal
VERILATOR_PREFIX ?= V$(verilator_top)
VERILATOR_OPT_CFLAGS ?= $(CUTTLESIM_OPT_FLAGS) $(if $(filter g++,$(CXX)),-flto,)
VERILATOR_OPT_LDFLAGS ?= $(VERILATOR_OPT_CFLAGS)
VERILATOR_TRACE_CFLAGS ?= $(VERILATOR_OPT_CFLAGS)
VERILATOR_TRACE_LDFLAGS ?= $(VERILATOR_OPT_LDFLAGS)
VERILATOR_OPT_FLAGS ?= --x-assign fast --x-initial fast --noassert -O3 -CFLAGS '$(VERILATOR_OPT_CFLAGS)' -LDFLAGS '$(VERILATOR_OPT_LDFLAGS)'
VERILATOR_TRACE_FLAGS ?= -CFLAGS '$(VERILATOR_TRACE_CFLAGS)' -LDFLAGS '$(VERILATOR_TRACE_LDFLAGS)'

ifneq (,$(findstring clang,$(CXX)))
verilator_compiler_flags := --compiler clang -CFLAGS -fPIC
else ifneq (,$(findstring g++,$(CXX)))
verilator_compiler_flags := --compiler gcc
else
verilator_compiler_flags :=
endif

verilator_top := $(basename $(notdir $(VERILATOR_TOP)))
verilator_driver := $(basename $(notdir $(VERILATOR_DRIVER)))
verilator_helper := verilator.hpp
verilator_cflags := -CFLAGS "-I $(shell pwd)"
verilator_prefix := $(VERILATOR_PREFIX)
verilator_prefix_flag := --prefix $(verilator_prefix)
verilator_flags := $(VERILATOR_FLAGS) $(VERILATOR_WARNINGS) $(verilator_cflags) $(verilator_prefix_flag) --cc --exe $(verilator_compiler_flags)
verilator_inputs := $(VERILATOR_DRIVER) $(VERILATOR_TOP)
verilator_deps := $(verilator_helper) $(verilator_inputs) $(wildcard *.sv) $(wildcard *.v)

$(verilator_optdir)/$(verilator_prefix).mk: $(verilator_deps)
	verilator $(verilator_flags) --Mdir $(verilator_optdir) $(VERILATOR_OPT_FLAGS) $(verilator_inputs)

$(verilator_tracedir)/$(verilator_prefix).mk: $(verilator_deps)
	verilator $(verilator_flags) --Mdir $(verilator_tracedir) -CFLAGS "-DTRACE" --trace $(VERILATOR_TRACE_FLAGS) $(verilator_inputs)

# $(verilator_deps) because verilator doesn't always update its Makefiles
$(verilator_optdir)/$(verilator_prefix): $(verilator_optdir)/$(verilator_prefix).mk $(verilator_deps)
	+$(MAKE) -C $(verilator_optdir) -f $(verilator_prefix).mk $(verilator_prefix)

$(verilator_tracedir)/$(verilator_prefix): $(verilator_tracedir)/$(verilator_prefix).mk $(verilator_deps)
	+$(MAKE) -C $(verilator_tracedir) -f $(verilator_prefix).mk $(verilator_prefix)

$(verilator_optdir)/$(verilator_prefix).xml: $(verilator_deps)
	verilator $(VERILATOR_WARNINGS) $(verilator_prefix_flag) -xml-only --bbox-sys --Mdir $(verilator_optdir) $(VERILATOR_TOP)

# Tracing
# =======

VERILATOR_ARGS ?=

verilator_invoke_opt := ./$(verilator_optdir)/$(verilator_prefix) $(VERILATOR_ARGS) $(NCYCLES)
verilator_invoke_trace := ./$(verilator_tracedir)/$(verilator_prefix) $(VERILATOR_ARGS) $(NCYCLES)

$(verilator_driver).run: $(verilator_optdir)/$(verilator_prefix)
	time $(verilator_invoke_opt)

$(verilator_driver).out: $(verilator_optdir)/$(verilator_prefix)
	time $(verilator_invoke_opt) > "$@"

$(verilator_driver).vcd: $(verilator_tracedir)/$(verilator_prefix)
	time $(verilator_invoke_trace) "$@"

ifeq (, $(shell which xml2stems))
$(verilator_driver).gtkwave: $(verilator_driver).vcd
	@echo "Warning: xml2stems not found: not showing rtlbrowse; try installing a more recent version of GTKWave."
	gtkwave -A --optimize $<
else
# Use xml2stems because Vermin only parses up to Verilog 1995 and we use [+:] from Verilog 2000
$(verilator_optdir)/$(verilator_prefix).stems: $(verilator_optdir)/$(verilator_prefix).xml
	xml2stems $< $@

$(verilator_driver).gtkwave: $(verilator_optdir)/$(verilator_prefix).stems $(verilator_driver).vcd
	gtkwave -A --optimize --stems $^
endif

twinwave: $(cuttlesim_driver).vcd $(verilator_driver).vcd
	twinwave -A $(cuttlesim_driver).vcd + -A $(verilator_driver).vcd

.PHONY: $(verilator_driver).run $(verilator_driver).gtkwave twinwave

# Cleanup
# =======

clean-verilator:
	rm -rf $(verilator_optdir)
	rm -rf $(verilator_tracedir)
	rm -f $(verilator_driver).vcd

#############
# Synthesis #
#############

YOSYS_FLAGS ?= -Q -T -v8
YOSYS_OPTS ?=
YOSYS_LIBDIRS ?= .

yosys_opts := $(YOSYS_FLAGS) $(YOSYS_OPTS)
yosys_libdir_args := $(patsubst %,-libdir %,$(YOSYS_LIBDIRS))

%.json.v: %.json
	yosys -p 'read_json -wideports $^; write_verilog $@'

# ICE40
# =====

ICE40_TOP ?= $(mod).ice40.v
ICE40_DEVICE ?= lp8k
ICE40_PACKAGE ?= cm81
ICE40_PCF ?= pins.pcf
ICE40_FREQUENCY ?= 48

ice40 := $(basename $(notdir $(ICE40_TOP)))

$(ice40).json: $(ICE40_TOP)
	yosys $(yosys_opts) -l $(ice40).json.log -p 'read_verilog $(ICE40_TOP); hierarchy $(yosys_libdir_args) -top $(ice40); synth_ice40 -retime -top $(ice40) -json $@'

$(ice40).asc: $(ICE40_PCF) $(ice40).json
	nextpnr-ice40 --$(ICE40_DEVICE) --freq $(ICE40_FREQUENCY) --opt-timing --timing-allow-fail --package $(ICE40_PACKAGE) --pcf $(ICE40_PCF) --seed 0 --asc $@ --json $(ice40).json

$(ice40).bit: $(ice40).asc
	icepack $< $@

$(ice40).rpt: $(ice40).asc
	icetime -d $(ICE40_DEVICE) -mtr $@ $<

clean-ice40:
	rm -f $(ice40).json
	rm -f $(ice40).json.log
	rm -f $(ice40).asc
	rm -f $(ice40).bit
	rm -f $(ice40).rpt
	rm -f $(ice40).json.v

# ECP5
# ====

ECP5_TOP ?= $(mod).ecp5.v
ECP5_DEVICE ?= 85k
ECP5_PACKAGE ?= CABGA381
ECP5_LPF ?= ulx3s_v20.lpf
ECP5_FREQUENCY ?= 25

ecp5 := $(basename $(notdir $(ECP5_TOP)))

yosys = yosys $(yosys_opts) -l $(2).json.log \
	-p 'read_verilog $(1); hierarchy $(yosys_libdir_args) -top $(2); $(3) -top $(2) -json $@'

$(ecp5).json: $(ecp5).v
	$(call yosys,$(ECP5_TOP),$(ecp5),synth_ecp5 -abc9)

$(ecp5).config: $(ecp5).json
	nextpnr-ecp5 --$(ECP5_DEVICE) --json $(ecp5).json --freq $(ECP5_FREQUENCY) \
		--package $(ECP5_PACKAGE) --lpf $(ECP5_LPF) --seed 0 --textcfg $(ecp5).config

$(ecp5).bit: $(ecp5).config
	ecppack --compress $< $@

clean-ecp5:
	rm -f $(ecp5).json
	rm -f $(ecp5).json.log
	rm -f $(ecp5).config
	rm -f $(ecp5).bit
	rm -f $(ecp5).json.v

###################
# Default targets #
###################

DEFAULT_TARGET ?= $(cuttlesim_driver).opt
default: $(DEFAULT_TARGET)

clean: clean-verilator clean-cuttlesim clean-ice40 clean-ecp5;

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
	@echo '      $(cuttlesim_driver).run:'
	@echo '        Run $(cuttlesim_driver).opt'
	@echo '      $(cuttlesim_driver).out:'
	@echo '        Output produced by $(cuttlesim_driver).opt'
	@echo '      $(cuttlesim_driver).vcd:'
	@echo '        VCD trace of $(cuttlesim_driver).opt'
	@echo '      $(cuttlesim_driver).gtkwave:'
	@echo '        View $(cuttlesim_driver).vcd'
	@echo '    Debugging'
	@echo '      gdb:'
	@echo '        Run $(cuttlesim_driver).debug under GDB'
	@echo '      lldb:'
	@echo '        Run $(cuttlesim_driver).debug under LLDB'
	@echo '      $(cuttlesim_driver).rr:'
	@echo '        Record execution of $(cuttlesim_driver).debug using rr'
	@echo '      rr:'
	@echo '        Replay rr trace of $(cuttlesim_driver).debug'
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
	@echo '      $(verilator_driver).run:'
	@echo '        Run $(verilator_optdir)/$(verilator_prefix)'
	@echo '      $(verilator_driver).vcd:'
	@echo '        VCD trace of $(verilator_tracedir)/$(verilator_prefix)'
	@echo '      $(verilator_driver).gtkwave:'
	@echo '        View $(verilator_driver).vcd'
	@echo '      twinwave:'
	@echo '        Compare the traces generated by Verilator and Cuttlesim'
	@echo '  Synthesis'
	@echo '    ICE40'
	@echo '      $(ice40).json:'
	@echo '        JSON netlist synthesized with Yosys for ICE40'
	@echo '      $(ice40).asc:'
	@echo '        ASC bitstream placed with nextpnr'
	@echo '      $(ice40).bit:'
	@echo '        ICE40 bitstream'
	@echo '      $(ice40).rpt:'
	@echo '        Timing report for $(ice40).asc'
	@echo '      $(ice40).json.v:'
	@echo '        Verilog rendering of $(ice40).json'
	@echo '    ECP5'
	@echo '      $(ecp5).json:'
	@echo '        JSON netlist synthesized with Yosys for ECP5'
	@echo '      $(ecp5).config:'
	@echo '        Trellis configuration placed with nextpnr'
	@echo '      $(ecp5).bit:'
	@echo '        ECP5 bitstream'
	@echo '      $(ecp5).json.v:'
	@echo '        Verilog rendering of $(ecp5).json'
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
	@echo '      CUTTLESIM_TRACE_FLAGS = $(CUTTLESIM_TRACE_FLAGS)'
	@echo '        C++ compiler flags used in trace mode'
	@echo '      CUTTLESIM_DEBUG_FLAGS = $(CUTTLESIM_DEBUG_FLAGS)'
	@echo '        C++ compiler flags used in debug mode'
	@echo '      CUTTLESIM_PERF_FLAGS = $(CUTTLESIM_PERF_FLAGS)'
	@echo '        C++ compiler flags used in perf mode (consider -DSIM_NOINLINE -Og)'
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
	@echo '      RR_RECORD_FLAGS = $(RR_RECORD_FLAGS)'
	@echo '        Command-line arguments passed to rr record'
	@echo '      RR_REPLAY_FLAGS = $(RR_REPLAY_FLAGS)'
	@echo '        Command-line arguments passed to rr replay'
	@echo '      PERF_FLAGS = $(PERF_FLAGS)'
	@echo '        Command-line arguments passed to perf'
	@echo '  Verilator'
	@echo '    Compiler settings'
	@echo '      VERILATOR_TOP = $(VERILATOR_TOP)'
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
	@echo '  Synthesis'
	@echo '    Yosys'
	@echo '      YOSYS_FLAGS = $(YOSYS_FLAGS)'
	@echo '        Flags passed to Yosys.'
	@echo '      YOSYS_OPTS = $(YOSYS_OPTS)'
	@echo '        Additional flags passed to Yosys.'
	@echo '      YOSYS_LIBDIRS = $(YOSYS_LIBDIRS)'
	@echo '        Directories passed as -libdir to the hierarchy command of Yosys'
	@echo '    ICE40 (IceStorm)'
	@echo '      Compiler settings'
	@echo '        ICE40_TOP = $(ICE40_TOP)'
	@echo '          Verilog or SystemVerilog file wrapping the code compiled by cuttlec.'
	@echo '        ICE40_DEVICE = $(ICE40_DEVICE)'
	@echo '          Device name passed to icetime and nextpnr-ice40.'
	@echo '        ICE40_PACKAGE = $(ICE40_PACKAGE)'
	@echo '          Package name passed to nextpnr-ice40.'
	@echo '        ICE40_PCF = $(ICE40_PCF)'
	@echo '          Physical contraints file passed to nextpnr-ice40.'
	@echo '    ECP5'
	@echo '      Compiler settings'
	@echo '        ECP5_TOP = $(ECP5_TOP)'
	@echo '          Verilog or SystemVerilog file wrapping the code compiled by cuttlec.'
	@echo '        ECP5_DEVICE = $(ECP5_DEVICE)'
	@echo '          Device name passed to nextpnr-ecp5.'
	@echo '        ECP5_PACKAGE = $(ECP5_PACKAGE)'
	@echo '          Package name passed to nextpnr.'
	@echo '        ECP5_LPF = $(ECP5_LPF)'
	@echo '          Physical contraints file passed to nextpnr.'

.PHONY: default clean-cuttlesim clean-verilog clean-ice40 clean-ecp5 clean help
