#ifdef NATIVE

#include <stdio.h>
int host_is_fpga() {
  return 0;
}

int led = 0;

int getled() {
  return led;
}

int putled(int on) {
  led = on;
  return on;
}

#else

static int* const UART_ADDR    = (int*)0x40000000;
static int* const LED_ADDR     = (int*)0x40000004;
static int* const STOP_ADDR    = (int*)0x40001000;

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
#endif

void putchars(const char* str) {
  while (*str)
    putchar(*str++);
}

void putln() {
  putchars("\r\n");
}
