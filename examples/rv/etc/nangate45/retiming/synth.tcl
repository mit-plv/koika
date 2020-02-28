yosys -import

set vdir $::env(YOSYS_LIBDIR)
set input $::env(VERILOG_INPUT)
set topmod $::env(VERILOG_TOP)
set libfile $::env(ABC_LIBFILE)

read_verilog $input
hierarchy -libdir $vdir -top $topmod

procs
flatten
opt
fsm
memory
techmap
opt

dfflibmap -prepare -liberty $libfile
abc -liberty $libfile -constr nangate45.constr -D 1 -dff -clk CLK -script abc_seq.script
dfflibmap -liberty $libfile

read_verilog multisize.v
hierarchy -top $topmod
procs
flatten
techmap

dfflibmap -liberty $libfile
abc -liberty $libfile -constr nangate45.constr -D 1 -dff -clk CLK -script abc.script

stat
