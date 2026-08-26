#include "smack.h"
#include <stdlib.h>

// @expect error

// Reading from a size-zero block is as invalid as writing to it.
int main(void) {
  char *p = malloc(0);
  char c = p[0];
  free(p);
  return c;
}
