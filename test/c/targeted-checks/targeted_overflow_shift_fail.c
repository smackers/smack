#include "smack.h"
#include <stdlib.h>

// @flag --checked-functions main compute
// @flag --check integer-overflow
// @expect error

int compute(int a, int b) { return a << b; }

int main() {
  int a = __VERIFIER_nondet_int();
  int b = __VERIFIER_nondet_int();
  return compute(a, b);
}
