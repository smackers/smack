#include "smack-contracts.h"
#include "smack.h"
#include <stdio.h>
#include <stdlib.h>

// @expect error

int g;

void p() {
  ensures(g == 0 && g == 1);
  g = 0;
}
