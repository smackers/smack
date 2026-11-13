#include "smack.h"

// @expect error
// @checkbpl grep -q lambda

// The bug is only reachable after four iterations, beyond --unroll=1: with
// the loop kept, the code after it is unreachable and the program is
// vacuously verified. Only the summary finds it.
int main(void) {
  unsigned a[4];
  unsigned n = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(n == 4);

  for (unsigned i = 0; i < n; ++i)
    a[i] = 0;

  __VERIFIER_assert(a[3] == 1);
  return 0;
}
