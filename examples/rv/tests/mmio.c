static int* const PUT_ADDR = (int *)0x40000000;
static int* const STOP_ADDR = (int *)0x40001000;

int getchar() {
  return 0;
}

void __attribute__((noreturn)) exit(int code) {
  *STOP_ADDR = code;
  __builtin_unreachable();
}

int putchar(int c) {
  *PUT_ADDR = c;
  return c;
}
