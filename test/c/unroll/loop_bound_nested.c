#include "smack.h"

// @expect verified
// @checkout grep -F "main: --unroll=5 is needed to explore it fully"
// @checkout grep -F "main: --unroll=4 is needed to explore it fully"

// Both loops of the nest have to be reported, each with its own bound. Walking
// LoopInfo with begin()/end() would visit only the outermost loop and miss the
// inner one entirely -- which is backwards, since in a nest it is usually the
// inner loop that needs the larger bound. The two loops are given different
// trip counts here (5 and 4) precisely so that one warning cannot stand in for
// the other.

int main(void) {
  int a;
  int b;
  int c = 0;

  for (a = 0; a < 4; a++)
    for (b = 0; b < 3; b++)
      c++;

  return c;
}
