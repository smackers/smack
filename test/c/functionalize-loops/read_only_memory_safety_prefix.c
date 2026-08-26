#include "smack.h"

// @expect verified
// @flag --check=memory-safety
// @checkbpl grep -q "functional read-only loop summary for stop_immediately"
// @checkbpl grep -q "functional.firstStop"
// @checkout awk '/SMACK warning: found loop/ {x=1} END{exit x}'

static int stop_immediately(const unsigned char *a, unsigned n) {
  for (unsigned i = 0; i < n; ++i)
    if (a[i] != 0)
      return 0;
  return 1;
}

int main(void) {
  unsigned char a[1];
  unsigned n = __VERIFIER_nondet_unsigned();
  a[0] = 1;
  __VERIFIER_assume(n > 0);
  return stop_immediately(a, n);
}
