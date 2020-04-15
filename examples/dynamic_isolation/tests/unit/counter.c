#include "../mmio.h"

int main() {
  for (int i = 32; i < 128; i++) {
    putchar(i);
    putchar('\n');
  }
}
