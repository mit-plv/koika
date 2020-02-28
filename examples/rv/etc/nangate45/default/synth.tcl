yosys -import

set vdir $::env(YOSYS_LIBDIR)
set input $::env(VERILOG_INPUT)
set topmod $::env(VERILOG_TOP)
set libfile $::env(ABC_LIBFILE)

read_verilog $input
hierarchy -libdir $vdir -top $topmod

procs
flatten
opt_clean -purge
opt -full -purge
fsm
memory
techmap
opt -full -purge

dfflibmap -liberty $libfile
abc -liberty $libfile -constr nangate45.constr -dff -script nangate45.abc

stat
