#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

// @expect 1 verified, 1 errors?

int g;

void p() {
  ensures(g == old(g));
  g++;
}

int main(void) {
  p();
  return 0;
}