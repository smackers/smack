#include "smack.h"
#include <assert.h>
#include <fenv.h>

// @expect error

int main(void) {
  int rm = fegetround();
  assume(rm != FE_DOWNWARD && rm != FE_UPWARD && rm != FE_TOWARDZERO);

  assert(rm < 0);

  return 0;
}
