#include "smack.h"
#include <assert.h>

// @expect verified
// @checkbpl grep -q lambda

static void copy_add(unsigned *restrict dst, const unsigned *restrict src,
                     unsigned n, unsigned c) {
  for (unsigned i = 0; i < n; ++i)
    dst[i] = src[i] + c;
}

int main(void) {
  unsigned dst[4096];
  unsigned src[4096];
  unsigned n = __VERIFIER_nondet_unsigned();
  unsigned j = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(n <= 4096);
  __VERIFIER_assume(j < n);

  copy_add(dst, src, n, 1);

  assert(dst[j] == src[j] + 1);
  return 0;
}
