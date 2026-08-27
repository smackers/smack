#include "smack.h"
#include <assert.h>

// @expect verified
// @flag --check=memory-safety
// @checkbpl grep -q "functional affine access range checks"
// @checkbpl grep -q "functional loop summary for main"
// @checkout awk '/SMACK warning: found loop/ {x=1} END{exit x}'

int main(void) {
  unsigned a[4096];
  unsigned n = __VERIFIER_nondet_unsigned();
  unsigned j = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(n <= 4096);
  __VERIFIER_assume(j < n);

  for (unsigned i = 0; i < n; ++i)
    a[i] = 0;

  assert(a[j] == 0);
  return 0;
}
