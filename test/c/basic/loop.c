#include "smack.h"
#include <stdio.h>
#include <stdlib.h>

// @flag --loop-limit=11
// @flag --unroll=11
// @expect verified

#define MAXSIZE 10

int x;

int main() {
  int i = 0;

  x = 0;

  for (i = 0; i < MAXSIZE; i++) {
    x = i;
  }
  assert(x == MAXSIZE - 1);
  return 0;
}
