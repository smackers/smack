#include <stdio.h>
#include <stdlib.h>
#include <smack.h>
#include <smack-contracts.h>

// @expect 1 verified, 0 errors?

int g;

int p() {
  requires(g > 0);
  ensures(result() > 10);
  return g + 10;
}
