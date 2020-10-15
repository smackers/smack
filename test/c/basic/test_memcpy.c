#include "smack.h"
#include <assert.h>
#include <string.h>

// @expect verified

int main(void) {
  int a = __VERIFIER_nondet_int();
  int b = __VERIFIER_nondet_int();
  memcpy(&a, &b, sizeof(int));
  assert(a == b);
  return 0;
}
