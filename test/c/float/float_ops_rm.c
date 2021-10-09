#include "smack.h"
#include <assert.h>
#include <fenv.h>

// @expect verified

int main(void) {
  double d = 1.999999999999;
  fesetround(FE_UPWARD);
  float f = d;
  assert(f == 2);
  return 0;
}
