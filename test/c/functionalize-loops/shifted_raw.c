#include "smack.h"

// @expect verified
// @checkbpl awk 'index($0,"functional loop summary for main"){found=1} END{exit found}'
// @checkout grep -F "SMACK warning: found loop"

int main(void) {
  unsigned a[4096];
  unsigned n = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(n < 4096);

  for (unsigned i = 0; i < n; ++i)
    a[i + 1] = a[i] + 1;

  return 0;
}
