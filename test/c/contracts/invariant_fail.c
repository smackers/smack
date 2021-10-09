#include "smack-contracts.h"
#include "smack.h"
#include <stdio.h>
#include <stdlib.h>

// @expect error

int g[10];

int main(void) {

  for (int i = 0; i < 4; i++) {
    invariant(i < 4);
    g[i] = i;
  }

  return 0;
}
