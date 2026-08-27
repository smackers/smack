#include "smack.h"
#include <stdarg.h>

// @expect verified

// A nondeterministic value travels through the list rather than being
// replaced by an arbitrary one.
static int first(int n, ...) {
  va_list ap;
  va_start(ap, n);
  int v = va_arg(ap, int);
  va_end(ap);
  return v;
}

int main(void) {
  int k = __VERIFIER_nondet_int();
  __VERIFIER_assume(k > 5);
  __VERIFIER_assert(first(1, k) > 5);
  return 0;
}
