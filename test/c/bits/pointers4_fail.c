#include "smack.h"
#include <stdio.h>
#include <stdlib.h>

// @expect error

int main() {
  int *a = (int *)malloc(sizeof(int));

  *a = 256;
  *((char *)a + 1) = 1;
  assert(*a == 257);
  free(a);
  return 0;
}
