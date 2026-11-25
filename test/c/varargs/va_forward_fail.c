#include "smack.h"
#include <stdarg.h>

// @expect error

static int inner(int n, va_list ap) { return va_arg(ap, int); }

static int outer(int n, ...) {
  va_list ap;
  va_start(ap, n);
  int v = inner(n, ap);
  va_end(ap);
  return v;
}

int main(void) {
  __VERIFIER_assert(outer(1, 7) == 8);
  return 0;
}
