#include "smack-contracts.h"
#include "smack.h"
#include <stdio.h>
#include <stdlib.h>

// @expect verified

int g;

void p() {
  ensures(g > old(g));
  g++;
}

int main(void) {
  p();
  return 0;
}
