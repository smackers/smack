#include "smack.h"
#include <assert.h>

// @expect verified
// @flag --check=memory-safety
// @checkbpl grep -q "functional read-only assertion loop summary for check"
// @checkbpl grep -q "functional.read.check"
// @checkout awk '/SMACK warning: found loop/ {x=1} END{exit x}'

static void check(const unsigned char *a, unsigned n) {
  for (unsigned i = 0; i < n; ++i)
    assert(a[i] == 0);
}

int main(void) {
  unsigned char a[4096];
  unsigned n = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(n <= 4096);
  for (unsigned i = 0; i < n; ++i)
    a[i] = 0;
  check(a, n);
  return 0;
}
