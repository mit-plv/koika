static int* const UART_ADDR = (int*)0x40000000;
static int* const LED_ADDR  = (int*)0x40000004;
static int* const STOP_ADDR = (int*)0x40001000;

int getchar1() {
  return 0;
}

void __attribute__((noreturn)) exit1(int code) {
  *STOP_ADDR = code;
  __builtin_unreachable();
}

int putchar1(int c) {
  *UART_ADDR = c;
  return c;
}

int getled1() {
  return *LED_ADDR;
}

int putled1(int on) {
  *LED_ADDR = on;
  return on;
}

static inline __attribute__((unused)) void putchars1(const char* str) {
  while (*str) {
    putchar1(*str);
    str++;
  }
}
