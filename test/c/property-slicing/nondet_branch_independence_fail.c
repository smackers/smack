#include "smack.h"

// @expect error

// Two property-irrelevant loops whose header branches must take OPPOSITE truth
// values for control to reach the assertion: the first is left by falling out
// of its test, the second by taking its test. The slicer nondeterminizes both
// conditions. If the two sites share one value -- as they did when the
// replacement was an LLVM `undef`, which SMACK emits as a single module-global
// Boogie constant per type -- the assertion is unreachable and this real error
// is reported verified.
int main(void) {
  int n = __VERIFIER_nondet_int();
  int m = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  int c1 = __VERIFIER_nondet_int();
  int c2 = __VERIFIER_nondet_int();
  int i = 0, j = 0;
  while (i < n) { /* stay while the test holds */
    if (c1)
      i++;
    else
      goto A;
  }
A:
  while (1) { /* leave when the test holds */
    if (j >= m)
      break;
    if (c2)
      goto B;
    else
      j++;
  }
B:
  __VERIFIER_assert(x != 5);
  return 0;
}
