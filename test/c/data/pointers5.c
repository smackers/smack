#include "smack.h"
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

// @expect verified

int main(void) {
  int *a = (int *)malloc(sizeof(int));
  intptr_t b;

  b = (intptr_t)a;
  *((int *)b) = 1;
  assert(*a == 1);
  free(a);
  return 0;
}
