#include "smack.h"

// @expect error
// @checkbpl grep -q "read-only assertion loop summary"

// The failing assertion is at iteration 3, beyond --unroll=1.
int main(void) {
  unsigned a[4];
  a[0] = 0;
  a[1] = 0;
  a[2] = 0;
  a[3] = 1;
  unsigned n = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(n == 4);

  for (unsigned i = 0; i < n; ++i)
    __VERIFIER_assert(a[i] == 0);

  return 0;
}
