#include "smack.h"

// @expect verified
// @checkbpl grep -q "read-only verifier loop summary"

// The assumption fails at iteration 2, so the assertion's failure at
// iteration 3 is never reached. The failure witness must see that an earlier
// iteration blocked, which needs the read-triggered form of the prefix.
int main(void) {
  unsigned a[4], b[4];
  a[0] = 0;
  a[1] = 0;
  a[2] = 1;
  a[3] = 0;
  b[0] = 0;
  b[1] = 0;
  b[2] = 0;
  b[3] = 1;

  for (unsigned i = 0; i < 4; ++i) {
    __VERIFIER_assume(a[i] == 0);
    __VERIFIER_assert(b[i] == 0);
  }

  return 0;
}
