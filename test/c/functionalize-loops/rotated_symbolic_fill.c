#include "smack.h"
#include <assert.h>

// @expect verified
// @flag --static-unroll
// @checkbpl grep -q lambda

int main(void) {
  unsigned a[4096];
  unsigned n = __VERIFIER_nondet_unsigned();
  unsigned j = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(0 < n);
  __VERIFIER_assume(n <= 4096);
  __VERIFIER_assume(j < n);

  for (unsigned i = 0; i < n; ++i)
    a[i] = 42;

  assert(a[j] == 42);
  return 0;
}
