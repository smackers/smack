#include "smack.h"
#include <stdarg.h>

// @expect verified

// A variadic function calls itself, so its copy has to call a copy as well.
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
  __VERIFIER_assert(count(1, 5) == 6);
  return 0;
}
