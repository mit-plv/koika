int* PUT_ADDR = (int *)0x00ffff0;
int* GET_ADDR = (int *)0x00ffff4;

int getchar() {
  return *GET_ADDR;
}

int putchar(int c) {
  *PUT_ADDR = c;
  return c;
}
