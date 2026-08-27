#include "smack.h"
#include <stdarg.h>

// @flag --float
// @expect verified

// A floating-point argument is promoted to double and read back as one.
static int isTwoAndAHalf(int n, ...) {
  va_list ap;
  va_start(ap, n);
  double d = va_arg(ap, double);
  va_end(ap);
  return d == 2.5;
}

int main(void) {
  __VERIFIER_assert(isTwoAndAHalf(1, 2.5) == 1);
  return 0;
}
