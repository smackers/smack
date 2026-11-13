#include "smack.h"

// @expect verified
// @flag --check=memory-safety
// @checkbpl grep -q "functional read-only verifier loop summary for check_one"
// @checkbpl grep -q "functional.firstStop"
// @checkout awk '/SMACK warning: found loop/ {x=1} END{exit x}'

static void check_one(const unsigned char *a, unsigned n) {
  for (unsigned i = 0; i < n; ++i) {
    __VERIFIER_assume(i == 0);
    __VERIFIER_assert(a[i] == 0);
  }
}

int main(void) {
  unsigned char a[1];
  a[0] = 0;
  check_one(a, 100);
  return 0;
}
