#include <stdio.h>
#include <stdlib.h>
#include <smack.h>
#include <smack-contracts.h>

// @skip
// @expect error

int g;

void p() {
  ensures(g == 0 && g == 1);
  g = 0;
}
