#include "smack.h"

// @expect error
// @flag --unroll=6

int main(void) {
  int c = 0;

  for (int a = 0; a < 5; a++)
    c++;

  for (int a = 0; a < 10; a++)
    c++;

  return c;
}
