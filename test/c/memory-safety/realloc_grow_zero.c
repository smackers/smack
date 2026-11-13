#include "smack.h"
#include <stdlib.h>

// @expect verified

// Growing a size-zero block through realloc yields an ordinary block.
int main(void) {
  char *p = malloc(0);
  char *q = realloc(p, 4);
  q[3] = 1;
  free(q);
  return 0;
}
