#include "smack.h"
#include <assert.h>
#include <fenv.h>

// @expect error

int main(void) {
  int rm = __VERIFIER_nondet_int();
  assume(rm != FE_TONEAREST && rm != FE_DOWNWARD && rm != FE_UPWARD);

  assert(fesetround(rm));

  return 0;
}
