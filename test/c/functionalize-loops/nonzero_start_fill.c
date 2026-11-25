#include "smack.h"
#include <assert.h>

// @expect verified
// @flag --static-unroll
// @checkbpl grep -q lambda

int main(void) {
  unsigned a[4096];
  unsigned start = __VERIFIER_nondet_unsigned();
  unsigned n = __VERIFIER_nondet_unsigned();
  unsigned j = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(start <= n);
  __VERIFIER_assume(n <= 4096);
  __VERIFIER_assume(start <= j);
  __VERIFIER_assume(j < n);

  unsigned i = start;
  for (; i < n; ++i)
    a[i] = i + 7;

  assert(a[j] == j + 7);
  assert(i == n);
  return 0;
}
