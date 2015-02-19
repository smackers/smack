#include <stdio.h>
#include <stdlib.h>
#include <smack.h>
#include <smack-contracts.h>

// @expect 1 verified, 0 errors?

int g[10];

int main(void) {
  ensures(forall("x", g[qvar("x")] == 0 || qvar("x") < 0 || qvar("x") > 9));
  return 0;
}