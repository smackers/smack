#include "smack.h"

// @expect verified
// @checkbpl awk '/lambda/ { found = 1 } END { exit found }'
// @checkout grep -F "SMACK warning: found loop"

int main(void) {
  unsigned a[64];
  unsigned n = __VERIFIER_nondet_unsigned();
  unsigned position = 0;
  __VERIFIER_assume(n <= 16);

  for (unsigned i = 0; i < n; ++i) {
    a[position++] = i;
    if (i & 1)
      a[position++] = 1;
    else
      a[position++] = 2;
    a[position++] = 3;
  }

  return 0;
}
