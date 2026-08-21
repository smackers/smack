#include "smack.h"

// @expect verified
// @flag --check=memory-safety
// @checkbpl grep -q "functional read-only loop summary for stop_late"
// @checkbpl grep -q "functional.firstStop"
// @checkout awk '/SMACK warning: found loop/ {x=1} END{exit x}'

static int stop_late(const unsigned char *a, unsigned n) {
  for (unsigned i = 0; i < n; ++i)
    if (a[i] != 0)
      return 0;
  return 1;
}

int main(void) {
  unsigned char a[6];
  a[0] = 0;
  a[1] = 0;
  a[2] = 0;
  a[3] = 0;
  a[4] = 0;
  a[5] = 1;
  return stop_late(a, 100);
}
