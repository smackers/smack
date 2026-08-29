#include "smack.h"
#include <stdarg.h>

// @expect error

static long pick(int n, ...) {
  va_list ap;
  va_start(ap, n);
  long a = va_arg(ap, long);
  long b = va_arg(ap, long);
  long c = va_arg(ap, long);
  va_end(ap);
  return a * 100 + b * 10 + c;
}

int main(void) {
  __VERIFIER_assert(pick(3, 1L, 2L, 3L) == 321);
  return 0;
}
