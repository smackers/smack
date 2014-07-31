#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

// @expect 3 verified, 1 errors?

int g[10];

int main(void) {
  ensures(forall("x", g[qvar("x")] == 0 || qvar("x") < 0 || qvar("x") > 9));
  return 0;
}