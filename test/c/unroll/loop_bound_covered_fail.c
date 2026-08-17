#include "smack.h"

// @expect error
// @flag --unroll=11
// @checkout awk '/SMACK warning: found loop/ { found = 1 } END { exit found }'

// The same loop as loop_bound_known.c, but now the bound covers every one of
// its executions, so there is nothing to warn about and the pass must stay
// silent. Note that plain `grep -v` would NOT check this -- it succeeds as
// soon as any one line fails to match -- hence the awk.
//
// The error is expected: --fail-on-loop-exit (from this directory's
// config.yml) asserts false at the loop exit, and at --unroll=11 that exit is
// finally reachable. That is the same 11 the warning asks for in
// loop_bound_known.c, which is the point of the pair.

int main(void) {
  int a;
  int b = 0;
  for (a = 0; a < 10; a++)
    b++;
  return b;
}
