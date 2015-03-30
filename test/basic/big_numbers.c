#include <smack.h>

// @flag --unroll=2
// @expect verified

int main() {
  int x = __VERIFIER_nondet_int();
  assert(x < x + 599147937792);
  return 0;
}