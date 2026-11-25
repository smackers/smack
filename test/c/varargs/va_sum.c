#include "smack.h"
#include <stdarg.h>

// @flag --unroll=5
// @expect verified

// va_arg in a loop: the list is walked, one slot at a time.
static int sum(int n, ...) {
  va_list ap;
  va_start(ap, n);
  int t = 0;
  for (int i = 0; i < n; i++)
    t += va_arg(ap, int);
  va_end(ap);
  return t;
}

int main(void) {
  __VERIFIER_assert(sum(3, 10, 20, 30) == 60);
  return 0;
}
