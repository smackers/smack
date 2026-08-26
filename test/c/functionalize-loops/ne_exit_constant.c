#include "smack.h"

// @expect verified
// @checkbpl grep -q lambda

// A constant count is the same number in modular and unbounded arithmetic, so
// an equality exit with a constant bound is still summarised.
int main(void) {
  unsigned a[8];
  unsigned j = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(j < 8);

  for (unsigned i = 0; i != 8; ++i)
    a[i] = 0;

  __VERIFIER_assert(a[j] == 0);
  return 0;
}
