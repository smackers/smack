#include "smack.h"

// @expect verified
// @flag --check=integer-overflow

int main(void) {
  unsigned int x = __VERIFIER_nondet_unsigned_int();
  unsigned int z = __VERIFIER_nondet_unsigned_int();

  assume(z < sizeof(x) * 8);
  return x << z;
}
