#include "smack.h"
#include <assert.h>

// @expect error
// @checkbpl grep -q "read-only assertion loop summary"
// @checkbpl grep -q "assert false"

static void assert_all_zero(const unsigned char *a, unsigned n) {
  for (unsigned i = 0; i < n; ++i)
    assert(a[i] == 0);
}

int main(void) {
  unsigned char a[4096];
  unsigned n = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(0 < n && n <= 4096);

  for (unsigned i = 0; i < n; ++i)
    a[i] = 0;
  unsigned k = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(k < n);
  a[k] = 1;
  assert_all_zero(a, n);
  return 0;
}
