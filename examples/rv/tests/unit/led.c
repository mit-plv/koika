#include "../mmio.h"

void wait(int duration) {
  for (int i = 0; i < duration; i++);
}

#define WAIT 200000

int main() {
  while (1) {
    putled(1);
    wait(WAIT);
    putled(0);
    wait(WAIT);
  }
}
