#include "smack.h"
#include <stdarg.h>

// @expect error

static int count(int n, ...) {
  va_list ap;
  va_start(ap, n);
  int v = va_arg(ap, int);
  va_end(ap);
  if (n == 0)
    return v;
  return count(n - 1, v + 1);
}

int main(void) {
  __VERIFIER_assert(count(1, 5) == 5);
  return 0;
}
