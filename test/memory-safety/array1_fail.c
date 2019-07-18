#include "smack.h"
#include <stdlib.h>

// @expect error

int main(void) {
  int *a = malloc(10 * sizeof(int));
  int b = a[10];
  free(a);
  return b;
}
