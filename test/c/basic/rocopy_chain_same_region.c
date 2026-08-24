#include "smack.h"
#include <string.h>

// @flag --memory-intrinsic-summaries
// @expect verified

// read-over-copy: chain of 22 memcpys within one region (each copy reads the previous copy's result); deeper than z3's qi.lazy_threshold

int main(void) {
  char b[23];
  char v = __VERIFIER_nondet_char();
  b[0] = v;
  b[1] = 0;
  b[2] = 0;
  b[3] = 0;
  b[4] = 0;
  b[5] = 0;
  b[6] = 0;
  b[7] = 0;
  b[8] = 0;
  b[9] = 0;
  b[10] = 0;
  b[11] = 0;
  b[12] = 0;
  b[13] = 0;
  b[14] = 0;
  b[15] = 0;
  b[16] = 0;
  b[17] = 0;
  b[18] = 0;
  b[19] = 0;
  b[20] = 0;
  b[21] = 0;
  b[22] = 0;
  memcpy(b + 1, b + 0, 1);
  memcpy(b + 2, b + 1, 1);
  memcpy(b + 3, b + 2, 1);
  memcpy(b + 4, b + 3, 1);
  memcpy(b + 5, b + 4, 1);
  memcpy(b + 6, b + 5, 1);
  memcpy(b + 7, b + 6, 1);
  memcpy(b + 8, b + 7, 1);
  memcpy(b + 9, b + 8, 1);
  memcpy(b + 10, b + 9, 1);
  memcpy(b + 11, b + 10, 1);
  memcpy(b + 12, b + 11, 1);
  memcpy(b + 13, b + 12, 1);
  memcpy(b + 14, b + 13, 1);
  memcpy(b + 15, b + 14, 1);
  memcpy(b + 16, b + 15, 1);
  memcpy(b + 17, b + 16, 1);
  memcpy(b + 18, b + 17, 1);
  memcpy(b + 19, b + 18, 1);
  memcpy(b + 20, b + 19, 1);
  memcpy(b + 21, b + 20, 1);
  memcpy(b + 22, b + 21, 1);
  __VERIFIER_assert(b[22] == v);
  return 0;
}
