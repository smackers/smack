#include "smack-contracts.h"
#include "smack.h"
#include <stdio.h>
#include <stdlib.h>

// @expect error

int g[10];

int main(void) {
  ensures(forall("x", g[qvar("x", int)] == 0 || qvar("x", int) < 0 ||
                          qvar("x", int) > 10));
  return 0;
}
