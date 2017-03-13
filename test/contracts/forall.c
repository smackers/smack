#include <stdio.h>
#include <stdlib.h>
#include <smack.h>
#include <smack-contracts.h>

// @expect verified

int g[10];

int main(void) {
  ensures(forall("x", g[qvar("x", int)] == 0 || qvar("x", int) < 0 || qvar("x", int) > 9));
  return 0;
}
