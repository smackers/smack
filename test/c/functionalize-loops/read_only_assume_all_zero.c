#include "smack.h"
#include <assert.h>

// @expect verified
// @flag --static-unroll
// @checkbpl grep -q "read-only assumption loop summary"
// @checkbpl awk '/functional.read.witness/{x=1}END{exit x}'

static void assume_all_zero(const unsigned char *a, unsigned n) {
  for (unsigned i = 0; i < n; ++i)
    __VERIFIER_assume(a[i] == 0);
}

int main(void) {
  unsigned char a[4096];
  unsigned n = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(n <= 4096);

  assume_all_zero(a, n);
  unsigned j = __VERIFIER_nondet_unsigned();
  if (j < n)
    assert(a[j] == 0);
  return 0;
}
