int putchar0(int c);

extern int _add_password(unsigned int id, char value);
extern char _lookup(unsigned int id);

int main0() {
  //set_enclave(0);
  _add_password(1, 'a');
  //set_enclave(0);
  //set_enclave(2);
  char ch = _lookup(1);
  //set_enclave(0);

  putchar0(ch);
  putchar0('\n');
  return 0;
}
