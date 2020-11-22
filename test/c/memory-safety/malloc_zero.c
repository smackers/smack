#include "smack.h"
#include <stdlib.h>

// @expect verified

int main(void) {
  int size = __VERIFIER_nondet_int();
  assume(size == 0);
  int *a = malloc(size);
  free(a);
  return size;
}
