static int* const UART_ADDR = (int*)0x40000000;

int putchar2(int c) {
  *UART_ADDR = c;
  return c;
}

static inline __attribute__((unused)) void putchars2(const char* str) {
  while (*str) {
    putchar2(*str);
    str++;
  }
}
