#include "smack.h"
#include <assert.h>

// @expect verified
// @flag --local-private-memory-maps
// @checkbpl grep -q 'var \$M\.L\.'

// Uses the CLI flag rather than -x svcomp so the assertion is actually
// checked: under the SVCOMP language mode, assert maps to a bodiless
// __VERIFIER_assert and the verification verdict is vacuous.

static int read_local(int value) {
  int local[2];
  local[0] = value;
  local[1] = value + 1;
  return local[0];
}

int main(void) {
  assert(read_local(42) == 42);
  return 0;
}
