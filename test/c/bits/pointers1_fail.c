#include "smack.h"
#include <stdlib.h>

// @expect error
// @flag --pointer-encoding=bit-vector

int main() {
  int *a = (int *)malloc(sizeof(int));
  int **p = (int **)malloc(sizeof(int *));
  *a = 256;
  *p = a;
  assert(**p + 1 != 257);
  free(a);
  return 0;
}
