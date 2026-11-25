#include "smack.h"
#include <stdarg.h>

// @expect error

static int walk(int n, ...) {
  va_list ap, aq;
  va_start(ap, n);
  int a = va_arg(ap, int);
  va_copy(aq, ap);
  int b = va_arg(ap, int);
  int c = va_arg(aq, int);
  int d = va_arg(aq, int);
  va_end(aq);
  va_end(ap);
  return a * 1000 + b * 100 + c * 10 + d;
}

int main(void) {
  __VERIFIER_assert(walk(3, 1, 2, 3) == 1233);
  return 0;
}
