#include "smack.h"

// @expect verified
// @flag --check=memory-safety
// @checkbpl grep -q "functional read-only verifier loop summary for blocked"
// @checkbpl grep -q "functional.firstStop"
// @checkout awk '/SMACK warning: found loop/ {x=1} END{exit x}'

static void blocked(const unsigned char *a, unsigned n) {
  unsigned stop = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(stop == 0);
  for (unsigned i = 0; i < n; ++i) {
    __VERIFIER_assume(stop != 0);
    __VERIFIER_assert(a[i] == 0);
  }
}

int main(void) {
  unsigned char a[1];
  blocked(a + 1, 100);
  return 0;
}
