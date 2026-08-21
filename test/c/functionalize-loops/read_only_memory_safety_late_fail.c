#include "smack.h"

// @expect error
// @flag --check=memory-safety
// @checkbpl grep -q "functional read-only loop summary for fail_late"
// @checkbpl grep -q "functional.firstStop"
// @checkout awk '/SMACK warning: found loop/ {x=1} END{exit x}'

static int fail_late(const unsigned char *a, unsigned n) {
  for (unsigned i = 0; i < n; ++i)
    if (a[i] != 0)
      return 0;
  return 1;
}

int main(void) {
  unsigned char a[4];
  a[0] = 0;
  a[1] = 0;
  a[2] = 0;
  a[3] = 0;
  return fail_late(a, 5);
}
