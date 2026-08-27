#include "smack.h"
#include <stdarg.h>

// @expect verified

// The va_list is handed to another function, as vfprintf does. The values
// live in memory, so the callee reads them.
static int inner(int n, va_list ap) { return va_arg(ap, int); }

static int outer(int n, ...) {
  va_list ap;
  va_start(ap, n);
  int v = inner(n, ap);
  va_end(ap);
  return v;
}

int main(void) {
  __VERIFIER_assert(outer(1, 7) == 7);
  return 0;
}
