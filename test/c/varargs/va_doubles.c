#include "smack.h"
#include <stdarg.h>

// @flag --float
// @expect verified

// More than one floating-point argument: the list is walked past the first.
static double sum2(int n, ...) {
  va_list ap;
  va_start(ap, n);
  double a = va_arg(ap, double);
  double b = va_arg(ap, double);
  va_end(ap);
  return a + b;
}

int main(void) {
  __VERIFIER_assert(sum2(2, 1.5, 2.5) == 4.0);
  return 0;
}
