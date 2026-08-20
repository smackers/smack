#include "smack.h"

// @expect verified
// @checkbpl awk 'index($0,"functional loop summary for copy"){found=1} END{exit found}'

static void copy(unsigned *dst, const unsigned *src, unsigned n) {
  for (unsigned i = 0; i < n; ++i)
    dst[i] = src[i];
}

int main(void) {
  unsigned a[4096];
  unsigned n = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(n < 4096);
  copy(a + 1, a, n);
  return 0;
}
