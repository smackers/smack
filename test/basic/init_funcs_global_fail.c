#include "smack.h"

// @expect error

int g = 10;

__SMACK_INIT(g1) {
  g = 11;
}

__SMACK_INIT(g2) {
  g = 12;
}

void main() {
  assert(g == 0 || g == 10 || g == 11);
}

