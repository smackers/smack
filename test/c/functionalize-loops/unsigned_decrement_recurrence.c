#include "smack.h"

// @expect verified
// @checkbpl grep -q lambda

// `s += 0xFFFFFFFFu` is an `add` without nsw, which SMACK lowers with the
// unsigned literal 4294967295; the summary's closed form must use the same
// representative or the values differ by 2^32 per iteration.
int main(void) {
  unsigned a[16];
  unsigned n = __VERIFIER_nondet_unsigned();
  unsigned j = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(n <= 16);
  __VERIFIER_assume(j < n);
  unsigned s = n;

  for (unsigned i = 0; i < n; ++i) {
    a[i] = s;
    s += 0xFFFFFFFFu;
  }

  __VERIFIER_assert(a[j] == n + 0xFFFFFFFFu * j);
  return 0;
}
