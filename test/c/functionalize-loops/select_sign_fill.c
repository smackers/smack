#include "smack.h"

// @expect verified
// @checkbpl grep -q lambda

// SMACK renders the constant arms of a select as unsigned magnitudes; the
// summarised store and the ordinary select after the loop must agree.
int main(void) {
  unsigned a[16], b[16];
  unsigned n = __VERIFIER_nondet_unsigned();
  unsigned j = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(n <= 16);
  __VERIFIER_assume(j < n);

  for (unsigned i = 0; i < n; ++i)
    a[i] = b[i] > 5 ? -1 : 0;

  __VERIFIER_assert(a[j] == (b[j] > 5 ? -1 : 0));
  return 0;
}
