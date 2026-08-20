#include "smack.h"

// @expect error
// @flag --check=memory-safety --unroll=2
// @checkbpl awk 'index($0,"functional read-only loop summary for bad_check"){found=1} END{exit found}'
// @checkout grep -F "SMACK warning: found loop"

static int bad_check(const unsigned char *a, unsigned n) {
  for (unsigned i = 0; i < n; ++i)
    if (a[i] != 0)
      return 0;
  return 1;
}

int main(void) {
  unsigned char a[4] = {0};
  return bad_check(a + 4, 1);
}
