static int* const SHARED_ADDR = (int*)0x00412340;

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
