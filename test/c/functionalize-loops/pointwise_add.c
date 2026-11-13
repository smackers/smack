#include "smack.h"
#include <assert.h>

// @expect verified
// @checkbpl grep -q lambda
// @checkout awk '/SMACK warning: found loop/ { found = 1 } END { exit found }'

int main(void) {
  unsigned a[4096];
  unsigned n = __VERIFIER_nondet_unsigned();
  unsigned j = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(n <= 4096);
  __VERIFIER_assume(j < n);
  unsigned old = a[j];

  for (unsigned i = 0; i < n; ++i)
    a[i] = a[i] + 1;

  assert(a[j] == old + 1);
  return 0;
}
