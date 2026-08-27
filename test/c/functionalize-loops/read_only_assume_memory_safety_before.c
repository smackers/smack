#include "smack.h"

// @expect verified
// @flag --check=memory-safety
// @checkbpl grep -q "assumption loop summary for stop_on_load"
// @checkbpl grep -q "functional.firstStop"
// @checkout awk '/SMACK warning: found loop/ {x=1} END{exit x}'

static void stop_on_load(const unsigned char *a, unsigned n) {
  for (unsigned i = 0; i < n; ++i)
    __VERIFIER_assume(a[i] != 0);
}

int main(void) {
  unsigned char a[1];
  a[0] = 0;
  stop_on_load(a, 100);
  return 0;
}
