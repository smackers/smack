#include "smack-contracts.h"
#include "smack.h"
#include <stdio.h>
#include <stdlib.h>

// @expect verified

int g;

int p() {
  requires(g > 0);
  ensures(result() > 10);
  return g + 10;
}
