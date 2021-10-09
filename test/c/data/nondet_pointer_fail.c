#include "smack.h"
#include <assert.h>

// @expect error

int main(void) {
  int *a;
  a = __VERIFIER_nondet();
  assert(a != 0);
  return 0;
}
