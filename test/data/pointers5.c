#include <stdlib.h>
#include <stdint.h>
#include "smack.h"

// @expect verified

int main(void) {
  int *a = (int*)malloc(sizeof(int));
  intptr_t b;
 
  b = (intptr_t)a;
  *((int *)b) = 1;
  assert(*a == 1);
  free(a);
  return 0;
}
