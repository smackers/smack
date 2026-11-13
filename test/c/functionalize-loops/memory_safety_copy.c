#include "smack.h"

// @expect verified
// @flag --check=memory-safety
// @checkbpl grep -q "functional affine access range checks"
// @checkbpl grep -q "functional loop summary for copy_add"
// @checkout awk '/SMACK warning: found loop/ {x=1} END{exit x}'

static void copy_add(unsigned *restrict dst, const unsigned *restrict src,
                     unsigned n) {
  for (unsigned i = 0; i < n; ++i)
    dst[i] = src[i] + 1;
}

int main(void) {
  unsigned dst[4096];
  unsigned src[4096];
  unsigned n = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(0 < n && n <= 4096);
  copy_add(dst, src, n);
  return dst[n - 1];
}
