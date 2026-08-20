#include "smack.h"
#include <assert.h>

// @expect verified
// @checkbpl awk '/functional loop summary for main/ { summaries++ } /:= \(lambda / { lambdas++ } END { exit !(summaries == 1 && lambdas == 2) }'

int main(void) {
  unsigned a[4096];
  unsigned b[4096];
  unsigned n = __VERIFIER_nondet_unsigned();
  unsigned j = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(n <= 4096);
  __VERIFIER_assume(j < n);
  unsigned old = a[j];

  for (unsigned i = 0; i < n; ++i) {
    b[i] = a[i];
    a[i] = 0;
  }

  assert(b[j] == old);
  assert(a[j] == 0);
  return 0;
}
