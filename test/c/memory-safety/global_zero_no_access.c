#include "smack.h"

// @expect verified

// Its neighbours stay accessible: giving the empty object a real size of
// zero must not disturb the objects placed around it.
int g[0];
int h[2];

int main(void) {
  h[0] = 1;
  h[1] = 2;
  return h[0] + h[1];
}
