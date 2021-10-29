#include "smack.h"

// @expect error
// @flag --unroll=11

int main(void) {
  int a;
  int b = 0;
  for (a = 0; a < 10; a++)
    b++;
  return b;
}
