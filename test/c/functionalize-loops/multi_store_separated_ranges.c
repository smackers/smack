#include "smack.h"
#include <assert.h>

// @expect verified
// @checkbpl grep -q lambda

int main(void) {
  unsigned a[2048];
  unsigned j = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(j < 1024);

  for (unsigned i = 0; i < 1024; ++i) {
    a[i] = i;
    a[i + 1024] = 0;
  }

  assert(a[j] == j);
  assert(a[j + 1024] == 0);
  return 0;
}
