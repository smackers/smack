#include "smack-contracts.h"
#include "smack.h"
#include <stdio.h>
#include <stdlib.h>

// @expect verified

int g;

void p() {
  ensures(g == 0 && g == 0);
  g = 0;
}
