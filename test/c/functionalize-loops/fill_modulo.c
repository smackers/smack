#include "smack.h"
#include <assert.h>

// @expect verified
// @flag --clang-options=-m32
// @checkbpl grep -q lambda

int main(void) {
  unsigned a[4096];
  unsigned n = __VERIFIER_nondet_unsigned();
  unsigned j = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(n <= 4096);
  __VERIFIER_assume(j < n);

  for (unsigned i = 0; i < n; ++i)
    a[i] = i % 3;

  assert(a[j] == j % 3);
  return 0;
}
