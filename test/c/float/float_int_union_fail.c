#include "smack.h"
#include <assert.h>

// @flag --integer-encoding=bit-vector
// @expect error

union mix {
  float f;
  int i;
};

int sum_to_int(float a, float b) {
  float sum = a + b;
  union mix m;
  m.f = sum;
  return m.i;
}

int main(void) {
  int i;
  i = sum_to_int(0x1.6b890ep+29, 0x1.6b890ep+29);
  assert(i == 0);
  return 0;
}
