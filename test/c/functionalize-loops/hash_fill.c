#include "smack.h"

// @expect verified
// @checkbpl grep -q lambda

// Multiplicative hashing: `i * 2654435761u` is a `mul` without nsw whose
// constant SMACK renders unsigned.
int main(void) {
  unsigned a[16];
  unsigned n = __VERIFIER_nondet_unsigned();
  unsigned j = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(n <= 16);
  __VERIFIER_assume(j < n);

  for (unsigned i = 0; i < n; ++i)
    a[i] = i * 2654435761u;

  __VERIFIER_assert(a[j] == j * 2654435761u);
  return 0;
}
