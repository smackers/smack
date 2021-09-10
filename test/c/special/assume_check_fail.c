#include "smack.h"
#include <assert.h>

// @expect error
// @flag --llvm-assumes=check
// @flag --integer-encoding=bit-vector

int main(void) {
  unsigned int x = __VERIFIER_nondet_unsigned_int();
  unsigned int y = __VERIFIER_nondet_unsigned_int();
  // This assumption is checked at verification time, and since
  // integer-encoding=bit-vector is enabled, the assumption should
  // be shown false.
  __builtin_assume((x ^ y) != (y ^ x));
  assert((x ^ y) != (y ^ x));
  return 0;
}
