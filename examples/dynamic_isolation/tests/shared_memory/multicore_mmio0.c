static int* const UART_ADDR = (int*)0x40000000;
static int* const LED_ADDR  = (int*)0x40000004;
static int* const STOP_ADDR = (int*)0x40001000;

int getchar0() {
  return 0;
}

void __attribute__((noreturn)) exit0(int code) {
  *STOP_ADDR = code;
  __builtin_unreachable();
}

int putchar0(int c) {
  *UART_ADDR = c;
  return c;
}

int getled0() {
  return *LED_ADDR;
}

int putled0(int on) {
  *LED_ADDR = on;
  return on;
}

static inline __attribute__((unused)) void putchars0(const char* str) {
  while (*str) {
    putchar0(*str);
    str++;
  }
}
