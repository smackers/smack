#include "smack.h"
#include <assert.h>

// @expect verified
// @checkbpl grep -q lambda

int main(void) {
  int a[4096];
  int b[4096];
  unsigned n = __VERIFIER_nondet_unsigned();
  unsigned j = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(n <= 4096);
  __VERIFIER_assume(j < n);

  for (unsigned i = 0; i < n; ++i) {
    int x = b[i];
    if (x > 0)
      a[i] = x;
    else
      a[i] = 0;
  }

  assert(a[j] == (b[j] > 0 ? b[j] : 0));
  return 0;
}
