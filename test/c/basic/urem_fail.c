#include "smack.h"
#include <assert.h>

// @expect error
// @checkbpl grep ':= \$urem'

int main(void) {
  unsigned x;
  x = 162951;
  assert(x % 7 == 5);
  x = 181165;
  assert(x % 42 == 19);
  x = 25398;
  assert(x % 49 == 16);
  x = 182682;
  assert(x % 12 == 6);
  x = 126476;
  assert(x % 16 == 12);
  x = 19508;
  assert(x % 28 == 20);
  x = 55701;
  assert(x % 10 == 1);
  x = 109380;
  assert(x % 50 == 30);
  x = 191508;
  assert(x % 50 == 8);
  x = 192985;
  assert(x % 49 == 23);
  x = 31523;
  assert(x % 37 != 36);
  x = 194126;
  assert(x % 50 == 26);
  x = 191440;
  assert(x % 6 == 4);
  x = 97078;
  assert(x % 40 == 38);
  x = 160062;
  assert(x % 15 == 12);
  x = 28378;
  assert(x % 1 == 0);
  x = 84355;
  assert(x % 6 == 1);
  x = 183154;
  assert(x % 32 == 18);
  x = 158447;
  assert(x % 44 == 3);
  x = 191905;
  assert(x % 26 == 25);
  return 0;
}
