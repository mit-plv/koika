# Require VERILOG_BSV to be set to the Verilog sources for bsc
bscflags = -keep-fires -aggressive-conditions -Xc++ -D_GLIBCXX_USE_CXX11_ABI=0
build_dir = bscdir

twiddleGen:
	mkdir -p bscdir
	bsc -simdir $(build_dir) -bdir $(build_dir) -sim -g mkGenerate -u GenerateTwiddle.bsv
	bsc -simdir $(build_dir) -bdir $(build_dir) -sim -e mkGenerate
	./a.out > generated

fftbsim:
	mkdir -p bscdir
	bsc -simdir $(build_dir) -bdir $(build_dir) -sim -O -Xc++ -O3 -Xc -O3 -g mkCombinationalFFT -p +:$(build_dir) -u FFT.bsv
	bsc -simdir $(build_dir) -bdir $(build_dir) -sim -O -Xc++ -O3 -Xc -O3 -e mkCombinationalFFT


fftverilog:
	mkdir -p bscdir
	bsc -vdir $(build_dir)  -u  -g mkCombinationalFFT -verilog -p +:$(build_dir) -u FFT.bsv
	verilator -y $(VERILOG_BSV) -O3 -CFLAGS -O3 -cc bscdir/mkCombinationalFFT.v	
	cd obj_dir; make -f VmkCombinationalFFT.mk; cd ..
	g++ -O3 -I obj_dir -I/usr/share/verilator/include driver.cpp /usr/share/verilator/include/verilated.cpp -o module obj_dir/VmkCombinationalFFT__ALL.a

clean:
	rm -rf *.bo
