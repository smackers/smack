#include "smack.h"
#include <stdlib.h>

// @expect error

void freeMemory(int *pointer) { free(pointer); }

int main(void) {
  int *a = malloc(10 * sizeof(int));
  int b;
  freeMemory(a);
  b = a[9];
  return b;
}
