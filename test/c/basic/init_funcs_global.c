#include "smack.h"
#include <assert.h>

// @expect verified

int g = 10;

__SMACK_INIT(g1) { g = 11; }

__SMACK_INIT(g2) { g = 12; }

int main(void) {
  assert(g == 12);
  return 0;
}
