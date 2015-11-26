#include "smack.h"

// @expect error

void no_printf(unsigned char *format, ...) { 
  assert (0 != 0);
  return;
}

void (*dprintf)(unsigned char *, ...) = &no_printf;

int main(void) {
  (*dprintf)((unsigned char *)"%d", 10);
  return 0;
}

