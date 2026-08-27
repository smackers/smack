#include "smack.h"
#include <assert.h>

// @expect verified
// @flag --static-unroll
// @checkbpl grep -q lambda

int main(void) {
  unsigned a[4096];
  unsigned start = 5;
  unsigned n = 2048;
  unsigned count = 1022;
  unsigned j = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(j < count);

  unsigned i = start;
  for (; i < n; i += 2)
    a[i] = i;

  assert(a[start + 2 * j] == start + 2 * j);
  assert(i == start + 2 * count);
  return 0;
}
