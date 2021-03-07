#include "../mmio.h"

#define WAIT 200000

int main() {
  do {
    putled(1);
    wait(WAIT);
    putled(0);
    wait(WAIT);
  } while (host_is_fpga());
}
