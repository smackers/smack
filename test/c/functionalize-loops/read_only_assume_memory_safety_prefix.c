#include "smack.h"

// @expect verified
// @flag --check=memory-safety
// @checkbpl awk '/functional read-only verifier loop summary for check_one/{x=1}END{exit x}'
// @checkout grep -F "SMACK warning: found loop"

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
