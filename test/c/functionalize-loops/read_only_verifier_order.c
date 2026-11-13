#include "smack.h"

// @expect verified
// @checkbpl grep -q "read-only verifier loop summary"

static void assume_then_assert(const unsigned char *a, unsigned n) {
  for (unsigned i = 0; i < n; ++i) {
    __VERIFIER_assume(a[i] == 0);
    __VERIFIER_assert(a[i] == 0);
  }
}

int main(void) {
  unsigned char a[4096];
  unsigned n = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(n <= 4096);
  assume_then_assert(a, n);
  return 0;
}
