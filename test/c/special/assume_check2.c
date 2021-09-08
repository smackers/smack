#include "smack.h"
#include <assert.h>

// @expect verified
// @flag --llvm-assumes=check
// @flag --integer-encoding=bit-vector

int main(void) {
  unsigned int x = __VERIFIER_nondet_unsigned_int();
  // This assumption is checked at verification time, and since
  // integer-encoding=bit-vector is enabled, the check will pass.
  __builtin_assume((x ^ x) == 0);
  assert((x ^ x) == 0);
  return 0;
}
