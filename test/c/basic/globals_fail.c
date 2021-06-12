#include "smack.h"
#include <assert.h>
#include <stdlib.h>

// @expect error

int g1;
int g2;

int main(void) {
  int *x = (int *)malloc(sizeof(int));

  g1 = 3;
  *x = 4;
  g2 = 5;
  assert(g1 != 3 || *x != 4 || g2 != 5);
}
