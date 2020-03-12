static int* const UART_ADDR = (int*)0x40000000;
static int* const LED_ADDR  = (int*)0x40000004;
static int* const STOP_ADDR = (int*)0x40001000;

int getchar() {
  return 0;
}

void __attribute__((noreturn)) exit(int code) {
  *STOP_ADDR = code;
  __builtin_unreachable();
}

int putchar(int c) {
  *UART_ADDR = c;
  return c;
}

int getled() {
  return *LED_ADDR;
}

int putled(int on) {
  *LED_ADDR = on;
  return on;
}

static inline __attribute__((unused)) void putchars(const char* str) {
  while (*str) {
    putchar(*str);
    str++;
  }
}
