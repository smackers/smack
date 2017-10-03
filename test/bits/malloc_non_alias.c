#include "smack.h"
#include <stdlib.h>

// @flag --bit-precise-pointers
// @expect verified

int main() {
  int* x = (int*)malloc(sizeof(int));
  int* y = (int*)malloc(sizeof(int));
  int* z = (int*)malloc(sizeof(int));
  if (x == y)
    y = z;
  *y = 1;
  *z = 2;
  assert(*y == 1);
  return 0;
}
