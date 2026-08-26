#include "smack.h"
#include <stdlib.h>
#include <string.h>

// @expect error

int main(void) {
  char src[1] = {1};
  char *p = malloc(0);
  memcpy(p, src, 1); // one byte into a block with none
  free(p);
  return 0;
}
