static int* const SHARED_ADDR = (int*)0x00031234;

int write_msg0(int c) {
  *SHARED_ADDR = c;
  return c;
}

int read_msg0() {
  return *SHARED_ADDR;
}

int putchar0(int c);

#define NUM_ITERS 1000
#define WAIT_TIME 50

int main0() {
  int msg;
  int expected = 1;
  write_msg0(0);

  while (expected < NUM_ITERS) {
    while ((msg = read_msg0()) != expected) {
      for (int i = 0; i< WAIT_TIME; i++) {
      }
    }
    write_msg0(++expected);
    putchar0('.');
    expected ++;
  }
  
}
/*
int main0() {
  int msg;
  write_msg0('X');
  while ((msg = read_msg0()) == 'X') {
  }

  if (msg == 'Y') {
    putchar0('Y');
    write_msg0('Z');
  } else {
    putchar0('1');
  }

  return 0;
}
*/
