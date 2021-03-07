#ifndef MMIO_H
#define MMIO_H

int getchar();
int putchar(int c);
void putchars(const char* str);
void putln();

int getled();
int putled(int on);

int host_is_fpga();
#endif
