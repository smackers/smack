#include "smack.h"
#include <stdlib.h>

// @expect error

int main(void) {
  int size = __VERIFIER_nondet_int();
  assume(size == 0);
  int *a = malloc(size);
  *a = 10;
  free(a);
  return size;
}
