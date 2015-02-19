#include <stdio.h>
#include <stdlib.h>
#include <smack.h>
#include <smack-contracts.h>

// @expect 1 verified, 0 errors?

#define SIZE 10
int g[SIZE];

void p() {
  ensures(forall("i", qvar("i") < 0 || qvar("i") >= SIZE || g[qvar("i")] == qvar("i")));

  for (int i=0; i<SIZE; i++) {
    invariant(forall("x", qvar("x") < 0 || qvar("x") >= i || g[qvar("x")] == qvar("x")));
    g[i] = i;
  }
}
