#include "smack.h"

// @expect verified
// @flag --check=integer-overflow

int main(void) {
  int x = __VERIFIER_nondet_int();
  int z = __VERIFIER_nondet_int();
  assume(x < 1024 && x >= 0);
  assume(0 <= z && z <= 21);
  return x << z;
}
