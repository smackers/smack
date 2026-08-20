#include "smack.h"

// @expect error
// @flag --check=memory-safety --unroll=2
// @checkbpl awk 'index($0,"functional loop summary for bad_fill"){found=1} END{exit found}'

static void bad_fill(unsigned *a, unsigned n) {
  for (unsigned i = 0; i < n; ++i)
    a[i] = 0;
}

int main(void) {
  unsigned a[4];
  bad_fill(a + 4, 1);
  return 0;
}
