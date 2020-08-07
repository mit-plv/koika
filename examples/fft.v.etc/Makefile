bscflags = -keep-fires -aggressive-conditions -Xc++ -D_GLIBCXX_USE_CXX11_ABI=0
build_dir = bscdir

twiddleGen:
	bsc -sim -g mkGenerate -u GenerateTwiddle.bsv
	bsc -sim -e mkGenerate
	./a.out > generated

fftbsim:
	bsc -sim -O -Xc++ -O3 -Xc -O3 -g mkCombinationalFFT -p +:$(bsvdir) -u FFT.bsv
	bsc -sim -O -Xc++ -O3 -Xc -O3 -e mkCombinationalFFT


fftverilog:
	bsc -u  -g mkCombinationalFFT -verilog -p +:$(bsvdir) -u FFT.bsv
	verilator -y /home/bthom/git/bsc/src/Verilog/ -O3 -CFLAGS -O3 -cc mkCombinationalFFT.v	
	cd obj_dir; make -f VmkCombinationalFFT.mk; cd ..
	g++ -O3 -I obj_dir -I/usr/share/verilator/include driver.cpp /usr/share/verilator/include/verilated.cpp -o module obj_dir/VmkCombinationalFFT__ALL.a

clean:
	rm -rf bscdir out out.so
