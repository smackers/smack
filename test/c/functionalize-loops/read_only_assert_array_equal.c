#include "smack.h"
#include <assert.h>

// @expect verified
// @checkbpl grep -q "read-only assertion loop summary"

static void assert_arrays_equal(const unsigned char *a, const unsigned char *b,
                                unsigned n) {
  for (unsigned i = 0; i < n; ++i)
    assert(a[i] == b[i]);
}

int main(void) {
  unsigned char a[4096];
  unsigned char b[4096];
  unsigned n = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(n <= 4096);

  for (unsigned i = 0; i < n; ++i)
    a[i] = b[i];
  assert_arrays_equal(a, b, n);
  return 0;
}
