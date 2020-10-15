#include "smack.h"
#include <assert.h>

// @expect verified

struct bla_s {
  int b1;
  int b2;
};

typedef struct bla_s bla_t;

int get_field(bla_t *bla) {
  int f = bla->b2;
  f = f >> 28;
  f = f & 0xF;
  return f;
}

void set_field(bla_t *bla, int f) {
  f = f & 0xF;
  f = f << 28;
  bla->b2 = ((bla->b2) & 0xFFFFFFF) | f;
}

int main(void) {
  bla_t bla;
  int f = get_field(&bla);
  set_field(&bla, f + 1);
  int g = get_field(&bla);
  assert(((f + 1) & 0xF) == (g & 0xF));
  return 0;
}
