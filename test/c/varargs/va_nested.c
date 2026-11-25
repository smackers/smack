#include "smack.h"
#include <stdarg.h>

// @expect verified

// One variadic function calls another. The caller is defined first, so that
// its copy is made while the call inside it is still to be rewritten: that
// call has to be found in the copy as well.
int inner(int n, ...);
int outer(int n, ...);

int main(void) {
  __VERIFIER_assert(outer(1, 7) == 8);
  return 0;
}

int outer(int n, ...) {
  va_list ap;
  va_start(ap, n);
  int v = va_arg(ap, int);
  va_end(ap);
  return inner(1, v + 1);
}

int inner(int n, ...) {
  va_list ap;
  va_start(ap, n);
  int v = va_arg(ap, int);
  va_end(ap);
  return v;
}
