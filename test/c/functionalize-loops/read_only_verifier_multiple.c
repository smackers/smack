#include "smack.h"
#include <assert.h>

// @expect verified
// @checkbpl grep -q "read-only verifier loop summary"

static void check_all(const unsigned char *a, const unsigned char *b,
                      unsigned n) {
  for (unsigned i = 0; i < n; ++i) {
    assume(a[i] == b[i]);
    assert(a[i] == 0);
    __VERIFIER_assert(b[i] == 0);
  }
}

int main(void) {
  unsigned char a[4096];
  unsigned char b[4096];
  unsigned n = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(n <= 4096);
  for (unsigned i = 0; i < n; ++i) {
    a[i] = 0;
    b[i] = 0;
  }
  check_all(a, b, n);
  return 0;
}
