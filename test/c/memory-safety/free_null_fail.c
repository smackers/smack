#include <stdlib.h>

// @expect error

int main(void) {
  int *a = NULL;
  free(a + 1);
  return 0;
}
