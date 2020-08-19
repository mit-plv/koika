#include "../multicore_mmio1.h"

const char* pattern1 = "-.- --- .. -.- .-";
#ifndef DOT
  #define DOT 20000
#endif

#ifndef DASH
  #define DASH (3 * DOT)
#endif

#ifndef SPACE_DOT
  #define SPACE DOT
#endif

#ifndef LETTER_SPACE
  #define LETTER_SPACE (3 * DOT)
#endif

#ifndef WORD_SPACE
  #define WORD_SPACE (7 * DOT)
#endif

void wait1(int duration) {
  for (int i = 0; i < duration; i++);
}

void blink(char c);
/*
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

  putled1(on);
  wait1(duration);
  putled1(0);
  wait1(SPACE);
}
*/

#ifndef REPEAT
  #define REPEAT 1
#endif

int main1() {
  for (int i = 0; i < REPEAT; i++) {
    wait1(WORD_SPACE);
    const char* p = pattern1;
    while (*p)
      blink(*p++);
  }
  putchar1('\n');
}
