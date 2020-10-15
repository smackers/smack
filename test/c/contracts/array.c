#include "smack-contracts.h"
#include "smack.h"
#include <stdio.h>
#include <stdlib.h>

// @expect verified

int g[10];

int main(void) {
  ensures(g[0] == 0);
  return 0;
}
