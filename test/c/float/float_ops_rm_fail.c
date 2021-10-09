#include "smack.h"
#include <assert.h>
#include <fenv.h>

// @expect error

int main(void) {
  double d = 1.999999999999;
  fesetround(FE_DOWNWARD);
  float f = d;
  assert(f == 2);
  return 0;
}
