#include "smack.h"
#include <assert.h>

// @expect verified

int main(void) {
  int i = 0;
  __sync_fetch_and_add(&i, 1);
  __sync_fetch_and_sub(&i, 1);
  __sync_fetch_and_or(&i, 1);
  __sync_fetch_and_and(&i, 1);
  __sync_fetch_and_xor(&i, 1);
  __sync_fetch_and_nand(&i, 1);
  assert(i == -1);
  return i;
}
