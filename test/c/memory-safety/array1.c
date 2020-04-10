#include "smack.h"
#include <stdlib.h>

// @expect verified

int main(void) {
  int *a = malloc(10 * sizeof(int));
  int b = a[9];
  free(a);
  return b;
}
