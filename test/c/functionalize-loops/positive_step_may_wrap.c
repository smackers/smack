#include "smack.h"

// @expect verified
// @flag --static-unroll
// @checkbpl awk 'index($0,"functional loop summary for main"){found=1} END{exit found}'

int main(void) {
  unsigned a[4096];
  unsigned n = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(n <= 4096);

  for (unsigned i = 0; i < n; i += 2)
    a[i] = i;

  return 0;
}
