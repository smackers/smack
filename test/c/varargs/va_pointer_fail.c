#include "smack.h"
#include <stdarg.h>

// @expect error

static int deref(int n, ...) {
  va_list ap;
  va_start(ap, n);
  int i = va_arg(ap, int);
  int *p = va_arg(ap, int *);
  va_end(ap);
  return i + *p;
}

int main(void) {
  int x = 9;
  __VERIFIER_assert(deref(2, 7, &x) == 17);
  return 0;
}
