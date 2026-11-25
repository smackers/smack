#include "smack.h"

// @expect error
// @flag --check=memory-safety
// @checkbpl grep -q "functional read-only loop summary for bad_check"
// @checkbpl grep -q "functional.firstStop"
// @checkout awk '/SMACK warning: found loop/ {x=1} END{exit x}'

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
