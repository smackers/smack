#include "smack.h"
#include <assert.h>
#include <stdlib.h>

// @expect verified

void foo(int *);
int *bar();

int main(void) {
  int *x = malloc(4);
  int *y = malloc(4);
  int *z;

  foo(y);
  z = bar(); // return of bar is not external!?!?
  *x = 1;
  *z = 2;
  assert(x != z);

  return 0;
}
