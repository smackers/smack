#include "smack.h"

// @expect error
// @flag --unroll=6

int func(int p) {
  int a = 0;
  while (a < 10) {
    if (a == p) break;
    a++;
  }
  return a;
}

int main(void) {
  int i = func(5);
  int j = func(15);

  return i + j;
}
