#include "smack.h"
#include <assert.h>

// @expect error

int g;

void no_printf(unsigned char *format, ...) {
  g = 1;
  return;
}

void (*dprintf)(unsigned char *, ...) = &no_printf;

int main(void) {
  (*dprintf)((unsigned char *)"%d", 10);
  assert(g == 0);
  return 0;
}
