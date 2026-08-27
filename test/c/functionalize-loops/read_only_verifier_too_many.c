#include "smack.h"

// @expect verified
// @checkbpl awk '/read-only.*summary for check/{x=1}END{exit x}'
// @checkout grep -F "SMACK warning: found loop"

static void check(const unsigned char *a, unsigned n) {
  for (unsigned i = 0; i < n; ++i) {
    __VERIFIER_assume(a[i] == 0);
    __VERIFIER_assume(a[i] <= 1);
    __VERIFIER_assume(a[i] <= 2);
    __VERIFIER_assume(a[i] <= 3);
    __VERIFIER_assume(a[i] <= 4);
  }
}

int main(void) {
  unsigned char a[4096];
  unsigned n = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(n <= 4096);
  check(a, n);
  return 0;
}
