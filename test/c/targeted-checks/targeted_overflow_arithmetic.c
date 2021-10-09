#include "smack.h"
#include <stdlib.h>

// @flag --checked-functions main
// @flag --check integer-overflow
// @expect verified

int compute(int a, int b) { return a + b; }

int main() {
  int a = __VERIFIER_nondet_int();
  int b = __VERIFIER_nondet_int();
  return compute(a, b);
}
