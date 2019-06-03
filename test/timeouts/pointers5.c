#include "smack.h"
#include <stdio.h>
#include <stdlib.h>

// @expect verified
// @flag --bit-precise-pointers

int main() {
  int *a = (int *)malloc(sizeof(int));
  long int b;

  b = (long int)a;
  *((int *)b) = 1;
  assert(*a == 1);
  free(a);
  return 0;
}
