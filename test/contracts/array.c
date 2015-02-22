#include <stdio.h>
#include <stdlib.h>
#include <smack.h>
#include <smack-contracts.h>

// @expect verified

int g[10];

int main(void) {
  ensures(g[0] == 0);
  return 0;
}