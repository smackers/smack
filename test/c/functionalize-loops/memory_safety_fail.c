#include "smack.h"

// @expect error
// @flag --check=memory-safety
// @checkbpl grep -q "functional affine access range checks"
// @checkbpl grep -q "functional loop summary for bad_fill"
// @checkout awk '/SMACK warning: found loop/ {x=1} END{exit x}'

static void bad_fill(unsigned *a, unsigned n) {
  for (unsigned i = 0; i < n; ++i)
    a[i] = 0;
}

int main(void) {
  unsigned a[4];
  bad_fill(a, 5);
  return 0;
}
