#include "smack.h"

// @expect error
// @flag --llvm-assumes=none

int main(void) {
  unsigned int y = 2 * (unsigned int)__VERIFIER_nondet_unsigned_short();
  // This assumption is not used, and since bit-precise is not enabled,
  // verification will fail.
  __builtin_assume((y & 1) == 0);
  __VERIFIER_assert((y & 1) == 0);
}
