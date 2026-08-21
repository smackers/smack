#include "smack.h"

// @expect verified
// @flag --check=memory-safety
// @checkbpl awk '/functional read-only loop summary for stop_immediately/{x=1}END{exit x}'
// @checkout grep -F "SMACK warning: found loop"

static int stop_immediately(const unsigned char *a, unsigned n) {
  for (unsigned i = 0; i < n; ++i)
    if (a[i] != 0)
      return 0;
  return 1;
}

int main(void) {
  unsigned char a[1];
  a[0] = 1;
  return stop_immediately(a, 100);
}
