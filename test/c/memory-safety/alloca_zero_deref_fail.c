#include "smack.h"
#include <stdlib.h>

// @expect error

// A variable-length array of length zero is a size-zero stack allocation;
// SV-COMP's rule covers alloca as well as malloc.
int main(void) {
  unsigned n = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(n == 0);
  char a[n];
  a[0] = 1;
  return 0;
}
