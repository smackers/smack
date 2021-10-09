#include "smack.h"
#include <assert.h>
#include <fenv.h>

// @expect verified

int main(void) {
  int rm = __VERIFIER_nondet_int();
  assume(rm != FE_TONEAREST && rm != FE_DOWNWARD && rm != FE_UPWARD &&
         rm != FE_TOWARDZERO);

  assert(fesetround(rm));

  return 0;
}
