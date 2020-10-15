#include "smack.h"
#include <assert.h>

// @expect verified
// @flag --llvm-assumes=check
// @flag --integer-encoding=bit-vector

int main(void) {
  unsigned int y = 2 * (unsigned int)__VERIFIER_nondet_unsigned_short();
  // This assumption is checked under integer-encoding=bit-vector and is
  // verified.
  __builtin_assume((y & 1) == 0);
  assert((y & 1) == 0);
}
