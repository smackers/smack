#include "smack.h"
#include <assert.h>

// @expect verified
// @checkbpl grep -q "functional read-only loop summary for all_zero"
// @checkbpl grep -q "forall.*functional.read.pointer"

static int all_zero(const unsigned char *a, unsigned n) {
  for (unsigned i = 0; i < n; ++i)
    if (a[i] != 0)
      return 0;
  return 1;
}

int main(void) {
  unsigned char a[4096];
  unsigned n = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(n <= 4096);

  int result = all_zero(a, n);
  unsigned j = __VERIFIER_nondet_unsigned();
  if (result && j < n)
    assert(a[j] == 0);

  if (n != 0) {
    unsigned k = __VERIFIER_nondet_unsigned();
    __VERIFIER_assume(k < n);
    a[k] = 1;
    assert(!all_zero(a, n));
  }
  return 0;
}
