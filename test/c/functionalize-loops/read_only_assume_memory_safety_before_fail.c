#include "smack.h"

// @expect error
// @flag --check=memory-safety
// @checkbpl grep -q "assumption loop summary for continue_to_load"
// @checkbpl grep -q "functional.firstStop"
// @checkout awk '/SMACK warning: found loop/ {x=1} END{exit x}'

static void continue_to_load(const unsigned char *a, unsigned n) {
  for (unsigned i = 0; i < n; ++i)
    __VERIFIER_assume(a[i] != 0);
}

int main(void) {
  unsigned char a[1];
  a[0] = 1;
  continue_to_load(a, 2);
  return 0;
}
