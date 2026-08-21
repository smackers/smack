#include "smack.h"

// @expect verified
// @flag --check=memory-safety
// @checkbpl grep -q "functional read-only loop summary for no_access"
// @checkbpl grep -q "functional.firstStop"
// @checkout awk '/SMACK warning: found loop/ {x=1} END{exit x}'

static int no_access(const unsigned char *a, unsigned n) {
  for (unsigned i = 0; i < n; ++i)
    if (a[i] != 0)
      return 0;
  return 1;
}

int main(void) {
  unsigned char a[1];
  return no_access(a + 1, 0);
}
