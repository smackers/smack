#include "smack.h"
#include <assert.h>

// @expect verified

typedef union {
  int v;
  struct {
    unsigned a : 8;
    unsigned b : 8;
    unsigned c : 8;
    unsigned d : 8;
  } i;
} bf;

int main(void) {
  bf b;
  b.v = __VERIFIER_nondet_int();
  assert(b.i.a == (b.v & 0xff));
  assert(b.i.b == ((b.v >> 8) & 0xff));
  assert(b.i.c == ((b.v >> 16) & 0xff));
  assert(b.i.d == ((b.v >> 24) & 0xff));
  return 0;
}
