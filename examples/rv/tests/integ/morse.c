#include "../mmio.h"

typedef struct {
  char letter;
  const char* code;
} pair;

const char* morse_code[26] = {
  ".-",   // 'A'
  "-...", // 'B'
  "-.-.", // 'C'
  "-..",  // 'D'
  ".",    // 'E'
  "..-.", // 'F'
  "--.",  // 'G'
  "....", // 'H'
  "..",   // 'I'
  ".---", // 'J'
  "-.-",  // 'K'
  ".-..", // 'L'
  "--",   // 'M'
  "-.",   // 'N'
  "---",  // 'O'
  ".--.", // 'P'
  "--.-", // 'Q'
  ".-.",  // 'R'
  "...",  // 'S'
  "-",    // 'T'
  "..-",  // 'U'
  "...-", // 'V'
  ".--",  // 'W'
  "-..-", // 'X'
  "-.--", // 'Y'
  "--..", // 'Z'
};

void beep(int on, int duration) {
  putled(on);
  wait(duration);
}

const char* morse_of_char(const char c) {
  return
    ('a' <= c && c <= 'z') ? morse_code[c - 'a'] :
    ('A' <= c && c <= 'Z') ? morse_code[c - 'A'] :
    0;
}

void tx1(const char letter, const int DOT) {
  int DASH = 3 * DOT;
  int SPACE = DOT;
  int WORD_SPACE = 7 * DOT;
  int LETTER_SPACE = 3 * DOT;

  const char* beeps = morse_of_char(letter);

  if (beeps) {
    while (*beeps) {
      switch (*beeps++) {
      case '.': beep(1, DOT); break;
      case '-': beep(1, DASH); break;
      }
      beep(0, SPACE);
    }
    wait(LETTER_SPACE - SPACE);
  } else {
    beep(0, WORD_SPACE);
  }
}

void tx(const char* message, const int DOT) {
  while (*message)
    tx1(*message++, DOT);
}

int main() {
  int DOT = host_is_fpga() ? 200000 : 5000;

  do {
    tx("KOIKA ", DOT);
  } while (host_is_fpga());
}
