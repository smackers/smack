#include <stdio.h>
#include <stdlib.h>
#include <smack.h>
#include <smack-contracts.h>

// @expect 0 verified, 1 errors?

int g[10];

int main(void) {
  ensures(g[0] == 1);
  return 0;
}