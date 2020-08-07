static int* const SHARED_ADDR = (int*)0x00400008;

int write_msg1(int c) {
  *SHARED_ADDR = c;
  return c;
}

int read_msg1() {
  return *SHARED_ADDR;
}


int putchar1(int c);

int main1() {
  int msg = read_msg1();
  putchar1('a');
  while (msg != 42) {
    msg = read_msg1();
  }
  putchar1('b');
  write_msg1(43);
  putchar1('c');
  return 0;
}
