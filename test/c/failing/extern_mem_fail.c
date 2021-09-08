#include "smack.h"
#include <assert.h>
#include <stdlib.h>

// @expect error

// see: https://github.com/smackers/smack/issues/553
void foo(int *);
int *bar();

int main() {
  int *x = malloc(4);
  int *y;

  foo(x);
  y = bar();

  *x = 1;
  *y = 2;

  assert(x != y);
}
