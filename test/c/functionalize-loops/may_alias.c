#include "smack.h"

// @expect verified
// @checkbpl awk '/summary for copy/{x=1}END{exit x}'

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
