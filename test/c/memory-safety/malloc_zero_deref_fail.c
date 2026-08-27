#include "smack.h"
#include <stdlib.h>

// @expect error

int main(void) {
  char *p = malloc(0);
  p[0] = 1; // a size-zero block cannot be accessed
  free(p);
  return 0;
}
