#include "smack.h"
#include <assert.h>
#include <stdlib.h>

// @flag --pointer-encoding=bit-vector
// @expect verified

int main(void) {
  int *x = (int *)malloc(sizeof(int));
  int *y = (int *)malloc(sizeof(int));
  int *z = (int *)malloc(sizeof(int));
  if (x == y)
    y = z;
  *y = 1;
  *z = 2;
  assert(*y == 1);
  return 0;
}
