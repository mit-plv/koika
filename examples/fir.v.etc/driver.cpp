#include <stdlib.h>
#include "Vmkfir.h"
#include "verilated.h"

int main(int argc, char **argv) {
  // Initialize Verilators variables
  Verilated::commandArgs(argc, argv);

  // Create an instance of our module under test
  Vmkfir *tb = new Vmkfir;
    tb->RST_N= 1;
    tb->eval();
 
    tb->RST_N= 0;
    tb->eval();
    tb->RST_N= 1;
    tb->eval();
  // Tick the clock until we are done
  int i = 0;
  while(i < 1000000000) {
    i++;
    tb->CLK= 1;
    tb->eval();
    tb->CLK = 0;
    tb->eval();
  }
  printf("%d", tb->rd);
  exit(EXIT_SUCCESS);
}
