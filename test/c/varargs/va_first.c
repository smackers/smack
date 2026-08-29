#include "smack.h"
#include <stdarg.h>

// @expect verified

// The value passed as a variadic argument is the value va_arg reads.
static int first(int n, ...) {
  va_list ap;
  va_start(ap, n);
  int v = va_arg(ap, int);
  va_end(ap);
  return v;
}

int main(void) {
  __VERIFIER_assert(first(1, 42) == 42);
  return 0;
}
