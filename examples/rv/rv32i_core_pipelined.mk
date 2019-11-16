default:
	g++ -O3 --std=c++14 -Wall -Wextra -fno-stack-protector -I rv32i_core_pipelined.v.objects rv_driver.cpp -o rv32i_core_pipelined.v.objects/rv_core.exe
