#include "smack.h"

// @expect error
// @flag --check=integer-overflow

int main(void) {
  int x = __VERIFIER_nondet_int();
  int z = 0;
  assume(x < 0);
  return x << z;
}
