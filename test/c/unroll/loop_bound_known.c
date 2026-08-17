#include "smack.h"

// @expect verified
// @checkout grep -F "main: --unroll=11 is needed to explore it fully"

// The loop runs a constant number of times, so ScalarEvolution can pin its
// trip count down exactly. The inherited --unroll=2 does not cover it, so the
// warning names the bound that would. This directory's config.yml also adds
// --fail-on-loop-exit, which independently confirms the prediction: the loop
// exit is unreachable at this bound, hence "verified" rather than an error.

int main(void) {
  int a;
  int b = 0;
  for (a = 0; a < 10; a++)
    b++;
  return b;
}
