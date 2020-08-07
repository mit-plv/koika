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
  for (int i = 0; i < 500; i++) {
  }
  int msg = read_msg1();
  putchar1(msg);
  /*
  putchar1('a');
  while (msg != 'X') {
    msg = read_msg1();
  }
  putchar1('b');
  write_msg1('Y');
  putchar1('c');
  */
  return 0;
}
