#include "smack.h"
#include <assert.h>
#include <stdlib.h>

// @expect verified

int main(void) {
  int *p = (int *)malloc(sizeof(int));
  *p = 2;
  p = (int *)realloc(p, sizeof(int));
  *p = 1;
  assert(*p != 2);
  return *p;
}
