#include "smack.h"
#include <assert.h>

// @expect error

int main(void) {
  int a = __VERIFIER_nondet_int();
  switch (a) {
  case 1:
    break;
  case 2:
    assert(0);
    break;
  default:
    break;
  }
  return 0;
}
