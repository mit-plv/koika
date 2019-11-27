int* PUT_ADDR = (int *)0x40000000;
int* STOP_ADDR = (int *)0x40001000;

int getchar() {
//  return *GET_ADDR;
}

int exit(int code) {
  *STOP_ADDR = code;
//  return *GET_ADDR;
}
int putchar(int c) {
  *PUT_ADDR = c;
  return c;
}
