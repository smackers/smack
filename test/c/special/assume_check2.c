#include "smack.h"
#include <assert.h>

// @expect verified
// @flag --llvm-assumes=check
// @flag --integer-encoding=bit-vector

int main(void) {
  unsigned int y = (2 * (unsigned int)__VERIFIER_nondet_unsigned_short()) + 1;
  // This assumption is checked at verification time, and since
  // integer-encoding=bit-vector is enabled, and y is clearly odd, the check
  // will pass.
  __builtin_assume((y & 1) == 1);
  assert((y & 1) == 1);
}
