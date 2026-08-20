#include "smack.h"
#include <assert.h>

// @expect verified
// @flag --static-unroll
// @checkbpl grep -q lambda

int main(void) {
  unsigned a[4096];
  unsigned n = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(n <= 4096);

  unsigned i = 0;
  for (; i < n; ++i)
    a[i] = 0;

  assert(i == n);
  return 0;
}
