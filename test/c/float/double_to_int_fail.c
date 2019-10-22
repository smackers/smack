#include "smack.h"

// @flag --bit-precise
// @expect error

int main(void) {
  double x = 1.5;
  int y = x;

  assert(y == 2);
}
