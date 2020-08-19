static int* const SHARED_ADDR = (int*)0x00031234;

int write_msg1(int c) {
  *SHARED_ADDR = c;
  return c;
}

int read_msg1() {
  return *SHARED_ADDR;
}

#define NUM_ITERS 1000
#define WAIT_TIME 50

int putchar1(int c);

int main1() {
  int msg;
  int expected = 0;

  for (int i = 0; i < WAIT_TIME; i++ ){
  }

  while (expected < NUM_ITERS) {
    while ((msg = read_msg1()) != expected) {
      for (int i = 0; i< WAIT_TIME; i++) {
      }
    }
    write_msg1(++expected);   
    putchar1('*');
    expected++;
  }
  
}

/*
int main1() {
  int msg;


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
*/
