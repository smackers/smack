#include "smack.h"
#include <fenv.h>

// @expect verified

int main(void) {
  assert(fegetround() == FE_TONEARESTEVEN);

  int rm = __VERIFIER_nondet_int();
  assume(rm >= 1 && rm <= 5);
  
  assert(!fesetround(rm));

  assert(fegetround() == rm);

  return 0;
}
