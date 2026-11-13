#include "smack.h"
#include <stdlib.h>

// @expect verified

// Without memory-safety checks the result of malloc(0) is still a fresh
// non-null pointer, distinct from every other allocation, under every
// memory model.
int main(void) {
  char *p = malloc(0);
  char *q = malloc(0);
  int *r = malloc(sizeof(int));
  __VERIFIER_assert(p != 0);
  __VERIFIER_assert(q != 0);
  __VERIFIER_assert(p != q);
  __VERIFIER_assert((void *)p != (void *)r);
  free(p);
  free(q);
  free(r);
  return 0;
}
