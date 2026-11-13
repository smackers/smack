#include "smack.h"
#include <assert.h>

// @expect verified
// @checkbpl grep -q lambda

int main(void) {
  unsigned a[4096];
  unsigned n = __VERIFIER_nondet_unsigned();
  unsigned j = __VERIFIER_nondet_unsigned();
  unsigned value = 0;
  __VERIFIER_assume(n <= 2048);
  __VERIFIER_assume(j < n);

  for (unsigned i = 0; i < n; ++i) {
    a[i] = value;
    value += 2;
  }

  assert(a[j] == 2 * j);
  return 0;
}
