default:
	g++ -O3 --std=c++14 -Wall -Wextra -fno-stack-protector -I RVCore.v.objects rv_driver.cpp -o rv_driver.exe
