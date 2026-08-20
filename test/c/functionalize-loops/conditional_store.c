#include "smack.h"
#include <assert.h>

// @expect verified
// @checkbpl grep -q lambda

int main(void) {
  unsigned a[4096];
  unsigned b[4096];
  unsigned n = __VERIFIER_nondet_unsigned();
  unsigned j = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(n <= 4096);
  __VERIFIER_assume(j < n);
  unsigned old = a[j];

  for (unsigned i = 0; i < n; ++i)
    if (b[i] != 0)
      a[i] = b[i];

  assert(a[j] == (b[j] != 0 ? b[j] : old));
  return 0;
}
