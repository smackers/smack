#include "smack.h"
#include <assert.h>

// @expect verified
// @checkbpl grep -q lambda

int main(void) {
  unsigned a[4096];
  unsigned n = __VERIFIER_nondet_unsigned();
  unsigned j = __VERIFIER_nondet_unsigned();
  unsigned k = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(n <= 4096);
  __VERIFIER_assume(j < n);
  __VERIFIER_assume(k < n);

  for (unsigned i = 0; i < n; ++i)
    a[i] = i;

  assert(a[j] == j);
  assert(a[k] == k);
  return 0;
}
