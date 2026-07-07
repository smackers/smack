#include "smack.h"

// @expect verified

int main(void) {
#pragma STDC FENV_ACCESS ON
  volatile float x = 2.0f;
  volatile float y = 1.0f;
  float z = x / y;
  (void)z;
  __VERIFIER_assert(1);
  return 0;
}
