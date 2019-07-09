#include "smack.h"
#include <stdlib.h>

// @expect error

int main(void) {
  int *a = malloc(10 * sizeof(int));
  int *b = malloc(10 * sizeof(int));
  int c = a[10];
  free(b);
  free(a);
  return c;
}
