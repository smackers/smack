#include <stdio.h>
#include <stdlib.h>
#include <smack.h>
#include <smack-contracts.h>

// @expect 1 verified, 0 errors?

int g[10];

int main(void) {

  for (int i=0; i<4; i++) {
    invariant(i <= 4);
    g[i] = i;
  }

  return 0;
}