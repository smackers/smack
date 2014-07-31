#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

// @expect 3 verified, 1 errors?

int g[10];

int main(void) {
  ensures(g[0] == 0);
  return 0;
}