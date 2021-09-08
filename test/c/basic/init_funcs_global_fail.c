#include "smack.h"
#include <assert.h>

// @expect error

int g = 10;

__SMACK_INIT(g1) { g = 11; }

__SMACK_INIT(g2) { g = 12; }

int main(void) {
  assert(g == 0 || g == 10 || g == 11);
  return 0;
}
