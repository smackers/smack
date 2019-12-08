#include "smack.h"

// @expect verified
// @flag --llvm-assumes=use

int main(void) {
  unsigned int y = 2 * (unsigned int)__VERIFIER_nondet_unsigned_short();
  // This assumption is used for verification, even though bit-precise
  // is not enabled, the assertion will pass.
  __builtin_assume((y & 1) == 0);
  assert((y & 1) == 0);
}
