#include "smack.h"
#include <assert.h>

// @expect error

int g = 0;

void set(void) { g = 11; }

int main(void) {
  set();
  assert(g != 11);
  return 0;
}
