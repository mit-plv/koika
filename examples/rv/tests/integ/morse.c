#include "../mmio.h"

const char* pattern = "-.- --- .. -.- .-";

void wait(int duration) {
  for (int i = 0; i < duration; i++);
}

void blink(char c, int DOT) {
  int on, duration;

  int DASH = (3 * DOT);
  int SPACE = DOT;
  int LETTER_SPACE = (3 * DOT);

  switch (c) {
  case '.':
    on = 1, duration = DOT;
    break;
  case '-':
    on = 1, duration = DASH;
    break;
  default:
    on = 0, duration = LETTER_SPACE;
    break;
  }

  putled(on);
  wait(duration);
  putled(0);
  wait(SPACE);
}

int main() {
  int DOT = host_is_fpga() ? 600000 : 20000;
  int WORD_SPACE = (7 * DOT);

  do {
    wait(WORD_SPACE);
    const char* p = pattern;
    while (*p)
      blink(*p++, DOT);
    putln();
  } while (host_is_fpga());
}
