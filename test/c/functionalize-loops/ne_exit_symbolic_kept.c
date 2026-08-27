#include "smack.h"

// @expect verified
// @checkbpl awk '/functional loop summary/{x=1}END{exit x}'

// ScalarEvolution's count for an `i != n` exit is `n - 0` modulo 2^32; under
// SMACK's unbounded integers the loop never exits when that count would wrap,
// so a symbolic equality exit must keep its loop.
int main(void) {
  unsigned a[16];
  unsigned n = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(n <= 16);

  for (unsigned i = 0; i != n; ++i)
    a[i] = 0;

  return 0;
}
