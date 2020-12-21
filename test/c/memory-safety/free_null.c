#include <stdlib.h>

// @expect verified

int main(void) {
  int *a = NULL;
  free(a);
  return 0;
}
