static int* const SHARED_ADDR = (int*)0x00031234;

int write_msg1(int c) {
  *SHARED_ADDR = c;
  return c;
}

int read_msg1() {
  return *SHARED_ADDR;
}


int putchar1(int c);

int main1() {
  for (int i = 0; i < 100; i++ ){
  }
  int msg = read_msg1();
  putchar1(msg);
  while (msg != 'X') {
    msg = read_msg1();
  }
  write_msg1('Y');

  while ((msg = read_msg1()) == 'Y') {
  }

  if (msg == 'Z') {
    putchar1('Z');
  } else {
    putchar1('4');
  }
  return 0;
}
