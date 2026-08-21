#include "smack.h"

// @expect error
// @flag --check=memory-safety
// @checkbpl grep -q "functional read-only verifier loop summary for check_between"
// @checkbpl grep -q "functional.firstStop"
// @checkout awk '/SMACK warning: found loop/ {x=1} END{exit x}'

static void check_between(const unsigned char *a, unsigned n) {
  for (unsigned i = 0; i < n; ++i) {
    __VERIFIER_assume(i < 2);
    __VERIFIER_assert(a[i] == 0);
    __VERIFIER_assume(i < 1);
  }
}

int main(void) {
  unsigned char a[1];
  a[0] = 0;
  check_between(a, 100);
  return 0;
}
