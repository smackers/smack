#include "smack.h"
#include <stdlib.h>

// @expect verified

// free(NULL) is a no-op (C11 7.22.3.3) and must leave every other block
// allocated; the spec-only $free of the reuse and no-reuse models used to
// frame $Alloc only for a non-null argument, so the free of p or q below
// failed its precondition. realloc(NULL, n) is the same idiom.
int main(void) {
  int *p = malloc(sizeof(int));
  *p = 1;
  free(0);
  int *q = realloc(0, sizeof(int));
  *q = 2;
  free(p);
  free(q);
  return 0;
}
