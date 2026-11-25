#include "smack.h"
#include <stdarg.h>

// @expect error

// A struct this large is passed by value in memory, a layout the model does
// not reproduce, so the call has to be left alone. Handing the callee the
// struct's address where it expects the struct's bytes would make its second
// field the 99 that follows, and this false claim would be proved.
struct big {
  long a, b, c;
};

static long second(int n, ...) {
  va_list ap;
  va_start(ap, n);
  struct big s = va_arg(ap, struct big);
  va_end(ap);
  return s.b;
}

int main(void) {
  struct big s = {1, 2, 3};
  __VERIFIER_assert(second(1, s, 99L) == 99);
  return 0;
}
