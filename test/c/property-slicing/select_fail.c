#include "smack.h"
#include <assert.h>

// @expect error

int main(void) {
  int c = __VERIFIER_nondet_int();
  int x = c ? 5 : 6;
  assert(x != 6);
  return 0;
}
