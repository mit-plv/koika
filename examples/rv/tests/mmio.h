#ifndef MMIO_H
#define MMIO_H

int getchar();
int putchar(int c);

static inline __attribute__((unused)) void puts(const char* str) {
  while (*str) {
    putchar(*str);
    str++;
  }
}
#endif
