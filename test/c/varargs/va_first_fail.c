#include "smack.h"
#include <stdarg.h>

// @expect error

static int first(int n, ...) {
  va_list ap;
  va_start(ap, n);
  int v = va_arg(ap, int);
  va_end(ap);
  return v;
}

int main(void) {
  __VERIFIER_assert(first(1, 42) == 43);
  return 0;
}
