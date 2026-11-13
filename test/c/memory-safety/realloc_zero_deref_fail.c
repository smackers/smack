#include "smack.h"
#include <stdlib.h>

// @expect error

// realloc(p, 0) frees p and returns a size-zero block; neither the old
// pointer nor the new one may be accessed.
int main(void) {
  char *p = malloc(4);
  char *q = realloc(p, 0);
  q[0] = 1;
  free(q);
  return 0;
}
