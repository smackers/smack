#include "smack.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

// @flag --loop-limit=11
// @flag --unroll=11
// @expect verified

#define MAXSIZE 10

int x;

int main() {
  int i = 0, j;

  x = 1;

  for (i = 0; i < MAXSIZE; i++) {
    j = i;
  }
  assert(x == 1);
  return 0;
}
