#include <stdio.h>
#include <stdlib.h>
#include <smack.h>
#include <smack-contracts.h>

// @expect 0 verified, 1 errors?

int g[10];

int main(void) {
  ensures(forall("x", g[qvar("x")] == 0 || qvar("x") < 0 || qvar("x") > 10));
  return 0;
}