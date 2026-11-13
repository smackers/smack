#include "smack.h"
#include <stdlib.h>

// @expect error

// A wider access does not change the picture: the block has no bytes.
int main(void) {
  int *p = malloc(0);
  *p = 1;
  free(p);
  return 0;
}
