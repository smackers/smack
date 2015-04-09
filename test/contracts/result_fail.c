#include <stdio.h>
#include <stdlib.h>
#include <smack.h>
#include <smack-contracts.h>

// @expect error

int g;

int p() {
  requires(g > 0);
  ensures(result() > 11);
  return g + 10;
}
