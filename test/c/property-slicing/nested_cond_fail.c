#include "smack.h"
#include <assert.h>

// @expect error
// Control dependence through nested conditions: the assertion has no data
// dependence on the predicates at all.

int main(void) {
  int a = __VERIFIER_nondet_int();
  int b = __VERIFIER_nondet_int();
  if (a > 0) {
    if (b > 0) {
      assert(0);
    }
  }
  return 0;
}
