#include "smack.h"

// @expect verified
// @flag --llvm-assumes=check
// @flag --bit-precise

int main(void) {
  unsigned int y = (2 * (unsigned int)__VERIFIER_nondet_unsigned_short()) + 1;
  // This assumption is checked at verification time, and since bit-precise
  // is enabled, and y is clearly odd, the check will pass.
  __builtin_assume((y & 1) == 1);
  assert((y & 1) == 1);
}
