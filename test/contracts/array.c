#include <stdio.h>
#include <stdlib.h>
#include <smack.h>
#include <smack-contracts.h>

// @expect 1 verified, 0 errors?

int g[10];

int main(void) {
  ensures(g[0] == 0);
  return 0;
}