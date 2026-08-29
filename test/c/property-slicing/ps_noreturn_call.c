#include "smack.h"
#include <assert.h>

// @expect verified
// The LDV `ldv_stop` idiom: an ordinary function -- no noreturn attribute --
// that never returns. It reaches no property root, has no unmodelled effect
// and writes no region, so every rule about dropping a call is satisfied; but
// dropping it lets the slice continue past a point the original never leaves,
// and the assertion below then fails for `guard == 0`.

void ldv_stop(void) {
  while (1) {
  }
}

int main(void) {
  int guard = __VERIFIER_nondet_int();
  if (!guard) {
    ldv_stop();
  }
  assert(guard != 0);
  return 0;
}
