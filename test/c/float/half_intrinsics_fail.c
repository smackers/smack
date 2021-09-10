#include "math.h"
#include "smack.h"
#include <assert.h>

// @flag --integer-encoding=bit-vector
// @expect error

int main(void) {
  union {
    unsigned short u;
    __fp16 h;
  } uh;
  uh.u = 1U;
  assert(isnormal((float)uh.h));
  assert(isnormal((double)uh.h));
  uh.h = 66504.0f;
  assert(uh.u != 31744U);
  uh.h = 66504.0;
  assert(uh.u == 31744U);
}
