# Require VERILOG_BSV to be set to the Verilog sources for bsc
build_dir = bscdir

firbsim:
	mkdir -p bscdir
	bsc -simdir $(build_dir) -bdir $(build_dir) -sim -O -Xc++ -O3 -Xc -O3 -g mkFir -p +:$(bsvdir) -u Fir.bsv
	bsc -simdir $(build_dir) -bdir $(build_dir) -sim -O -Xc++ -O3 -Xc -O3 -e mkFir


firverilog:
	mkdir -p bscdir
	bsc -vdir $(build_dir) -bdir $(build_dir)  -u  -g mkFir -verilog -p +:$(build_dir) -u Fir.bsv
	verilator -y $(VERILOG_BSV) -O3 -CFLAGS -O3 -cc $(build_dir)/mkFir.v	
	cd obj_dir; make -f VmkFir.mk; cd ..
	g++ -O3 -I obj_dir -I/usr/share/verilator/include driver.cpp /usr/share/verilator/include/verilated.cpp -o module obj_dir/VmkFir__ALL.a

clean:
	rm -rf *.bo
