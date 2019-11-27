int* PUT_ADDR = (int *)0x40000000;

int getchar() {
//  return *GET_ADDR;
}

int putchar(int c) {
  *PUT_ADDR = c;
  return c;
}
