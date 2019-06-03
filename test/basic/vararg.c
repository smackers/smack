#include "smack.h"
#include <stdarg.h>
#include <stdio.h>

// @expect verified

static void panic(int x, ...) {
  va_list args;
  va_start(args, x);
  printf("panic %d\n", x);
  printf("panic %d %d\n", x, va_arg(args, int));
  va_end(args);
  assert(x == 1);
}

int main(void) {
  panic(1);
  panic(1, 2);
  return 0;
}
