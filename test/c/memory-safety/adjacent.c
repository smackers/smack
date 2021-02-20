#include "smack.h"
#include <stdlib.h>

// @expect verified

int main(void) {
  int *a = malloc(10 * sizeof(int));
  int *b = malloc(10 * sizeof(int));
  int c = a[9];
  free(b);
  free(a);
  return c;
}
