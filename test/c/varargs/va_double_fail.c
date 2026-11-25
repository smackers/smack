#include "smack.h"
#include <stdarg.h>

// @flag --float
// @expect error

static int isTwoAndAHalf(int n, ...) {
  va_list ap;
  va_start(ap, n);
  double d = va_arg(ap, double);
  va_end(ap);
  return d == 2.5;
}

int main(void) {
  __VERIFIER_assert(isTwoAndAHalf(1, 3.5) == 1);
  return 0;
}
