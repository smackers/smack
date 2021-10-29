#include "smack.h"

// @expect verified
// @flag --unroll=5

int main(void) {
  int a;
  int b;
  int c = 0;
  for (a = 0; a < 5; a++)
    for (b = 0; b < 5; b++)
      c++;
  return c;
}
