#include <stddef.h>

// @expect verified
// @flag --clang-options="-O2 -Xclang -disable-llvm-passes"

typedef struct {
  char *p;
  size_t n;
} pair_t;

pair_t fun(void) {
  pair_t r;
  r.p = 0;
  r.n = 0;
  return r;
}

int main(void) {
  pair_t x = fun();
  return x.n != 0;
}
