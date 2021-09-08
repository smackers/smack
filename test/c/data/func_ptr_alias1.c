#include "smack.h"
#include <assert.h>

// @expect verified

int __incr(int x) { return ++x; }

int __decr(int x) { return --x; }

#ifdef __MACH__
int (*incr)(int) = __incr;
int (*decr)(int) = __decr;
#else
int incr(int) __attribute__((alias("__incr")));
int decr(int) __attribute__((alias("__decr")));
#endif

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
