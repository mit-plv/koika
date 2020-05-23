#define DB_SIZE 32

char db[DB_SIZE];

//__attribute__((__section__(".data.enclave1")));

//void __attribute__((__section__(".text.password_manager"))

int add_password(unsigned int id, char value) {
  if (id < DB_SIZE) {
    db[id] = value;
    return 0;
  } else {
    return 1;
  }
}

char lookup(unsigned int id) {
  if (id < DB_SIZE) {
    return db[id];
  } else {
    return 0;
  }
}
