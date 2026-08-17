#include "smack.h"
#include <assert.h>
#include <fenv.h>

// @expect verified
// @checkbpl grep "call __SMACK_init_func_initializeRoundingMode();"
// @checkbpl grep "\\$rmode := RNE;"

int main(void) {
  assert(fegetround() == FE_TONEAREST);
  return 0;
}
