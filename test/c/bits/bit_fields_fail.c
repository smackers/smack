#include "smack.h"
#include <assert.h>

// @expect error

typedef struct {
  unsigned int d : 5;
  unsigned int m : 4;
  unsigned int y;
} date;

int main(void) {
  date dt = {31, 11, 2014};
  assert(dt.d == 31);
  assert(dt.m == 12);
  assert(dt.y == 2014);
  return 0;
}
