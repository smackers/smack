#include "smack.h"
#include <assert.h>
#include <fenv.h>

// @expect verified

int main(void) {
  int rm = fegetround();
  assume(rm != FE_TONEAREST && rm != FE_DOWNWARD && rm != FE_UPWARD &&
         rm != FE_TOWARDZERO);

  assert(rm < 0);

  return 0;
}
