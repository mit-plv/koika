 #include "../multicore_mmio0.h"

const char* pattern = "-.- --- .. -.- .-";

#define DOT 20000
#define DASH (3 * DOT)
#define SPACE DOT
#define LETTER_SPACE (3 * DOT)
#define WORD_SPACE (7 * DOT)

void wait(int duration) {
  for (int i = 0; i < duration; i++);
}

void blink(char c) {
  int on, duration;

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

  putled0(on);
  wait(duration);
  putled0(0);
  wait(SPACE);
}

#define REPEAT 1

int main0() {
  for (int i = 0; i < REPEAT; i++) {
    wait(WORD_SPACE);
    const char* p = pattern;
    while (*p)
      blink(*p++);
  }
  putchar0('\n');
}
