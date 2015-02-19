#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

// @expect 2 verified, 0 errors?

int g;

void p() {
  ensures(g > old(g));
  g++;
}

int main(void) {
  p();
  return 0;
}