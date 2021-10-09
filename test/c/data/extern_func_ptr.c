#include "smack.h"
#include <assert.h>

// @expect verified

int *foo();

int main(void) {
  int *x = foo();
  int *y = foo();

  *x = 1;
  *y = 2;

  assert(*x == 1 || *x == 2);

  return 0;
}
