#include "smack.h"
#include <assert.h>

// @expect verified
// @checkbpl grep -q lambda

int main(void) {
  unsigned a[8192];
  unsigned long n = __VERIFIER_nondet_ulong();
  unsigned long j = __VERIFIER_nondet_ulong();
  __VERIFIER_assume(n <= 4096);
  __VERIFIER_assume(j < n);

  unsigned *p = a;
  for (unsigned long i = 0; i < n; ++i, p += 2) {
    p[0] = i;
    p[1] = 0;
  }

  assert(a[2 * j] == j);
  assert(a[2 * j + 1] == 0);
  return 0;
}
