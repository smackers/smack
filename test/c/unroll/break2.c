#include "smack.h"

// @expect verified
// @flag --unroll=4

int main(void) {
  int a = 1;
  while (a < 10) {
    if (a == 5) break;
    a++;
  }

  return a;
}
