#include "smack.h"
#include <stdlib.h>

// @expect verified
// @flag --clang-options=-m32 --bit-precise-pointers

int* a[2];

int main(void) {
  int b = 1;
  int** c = (int**)malloc(sizeof(int*));
  a[0] = &b;
  a[1] = &b;
  *c = a[0];
  assert(**c == 1);
  assert(*a[1] == 1);
  return 0;
}
