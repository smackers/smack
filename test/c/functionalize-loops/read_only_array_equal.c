#include "smack.h"
#include <assert.h>

// @expect verified
// @checkbpl grep -q "functional read-only loop summary for arrays_equal"

static int arrays_equal(const unsigned char *a, const unsigned char *b,
                        unsigned n) {
  for (unsigned i = 0; i < n; ++i)
    if (a[i] != b[i])
      return 0;
  return 1;
}

int main(void) {
  unsigned char a[4096];
  unsigned char b[4096];
  unsigned n = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(n <= 4096);

  int result = arrays_equal(a, b, n);
  unsigned j = __VERIFIER_nondet_unsigned();
  if (result && j < n)
    assert(a[j] == b[j]);

  if (n != 0) {
    unsigned k = __VERIFIER_nondet_unsigned();
    __VERIFIER_assume(k < n);
    a[k] = 0;
    b[k] = 1;
    assert(!arrays_equal(a, b, n));
  }
  return 0;
}
