#include "smack.h"
#include <assert.h>

// @expect error

int __incr(int x) { return x + 2; }

#ifdef __MACH__
int (*incr)(int) = __incr;
#else
int incr(int) __attribute__((alias("__incr")));
#endif

int main(void) {
  int x = __VERIFIER_nondet_int();
  int y = x;
  x = incr(x);
  assert(x == y + 1);
  return 0;
}
