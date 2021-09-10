#include "smack-contracts.h"
#include "smack.h"
#include <stdio.h>
#include <stdlib.h>

// @expect error

int g[10];

int main(void) {
  ensures(g[0] == 1);
  return 0;
}
