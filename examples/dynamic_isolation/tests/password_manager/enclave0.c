int putchar0(int c);

extern void set_enclave(int eid);
extern int _add_password(unsigned int id, char value);
extern char _lookup(unsigned int id);

int main0() {
  set_enclave(1);
  _add_password(1, 'a');
  set_enclave(0);
  set_enclave(1);
  char ch = _lookup(1);
  set_enclave(0);

  putchar0(ch);
  putchar0('\n');
}
