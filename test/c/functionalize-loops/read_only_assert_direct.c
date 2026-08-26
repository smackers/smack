#include "smack.h"

// @expect verified
// @flag --static-unroll
// @checkbpl grep -q "read-only assertion loop summary"
// @checkbpl grep -q "verifier.primitive"

static void verifier_assert_all_zero(const unsigned char *a, unsigned n) {
  for (unsigned i = 0; i < n; ++i)
    __VERIFIER_assert(a[i] == 0);
}

int main(void) {
  unsigned char a[4096];
  unsigned n = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(n <= 4096);

  for (unsigned i = 0; i < n; ++i)
    a[i] = 0;
  verifier_assert_all_zero(a, n);
  return 0;
}
