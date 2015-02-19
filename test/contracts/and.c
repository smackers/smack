#include <stdio.h>
#include <stdlib.h>
#include <smack.h>
#include <smack-contracts.h>

// @expect 1 verified, 0 errors?

int g;

void p() {
  ensures(g == 0 && g == 0);
  g = 0;
}
