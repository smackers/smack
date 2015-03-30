#include "smack.h"

// @expect verified
// @flag --unroll=1

int g = 10;

__SMACK_INIT(g1) {
  g = 11;
}

__SMACK_INIT(g2) {
  g = 12;
}

void main() {
  assert(g == 12);
}

