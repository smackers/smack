#include "smack.h"

// @expect verified

int incr(int x) { return ++x; }

int decr(int x) { return --x; }

int main(void) {
  int (*fp)(int);
  int x = 1, y = 1;

  if (y > 0) {
    fp = incr;
  } else {
    fp = decr;
  }
  x = fp(x);

  assert(x == 2);
  return 0;
}
