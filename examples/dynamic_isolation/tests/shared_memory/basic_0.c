static int* const SHARED_ADDR = (int*)0x00400008;

int write_msg0(int c) {
  *SHARED_ADDR = c;
  return c;
}

int read_msg0() {
  return *SHARED_ADDR;
}

int putchar0(int c);

int main0() {
  int msg;
  write_msg0('X');
  
  /*
  putchar0('A');
  while ((msg = read_msg0()) == 'X') {
  }
  putchar0('B');
  
  if (msg == 'Y') {
    putchar0('C');
  } else {
    putchar0(msg);
 }
 */
  
  return 0;
}
