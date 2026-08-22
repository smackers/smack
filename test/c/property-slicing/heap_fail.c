#include "smack.h"
#include <assert.h>
#include <stdlib.h>

// @expect error

int main(void) {
  int *p = (int *)malloc(sizeof(int));
  *p = 3;
  int v = *p;
  free(p);
  assert(v != 3);
  return 0;
}
