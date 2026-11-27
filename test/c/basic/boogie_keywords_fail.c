#include "smack.h"
#include <assert.h>

// @expect error

// Globals and functions whose names are Boogie 3 keywords; SMACK must rename
// them before Boogie parses the program (issue #842).

static char action[16];
int asserts, datatype, hideable, is, measure, preserves, pure, refines,
    revealed, uses;
int RNA, RNE, RTN, RTP, RTZ;
int roundNearestTiesToAway, roundNearestTiesToEven, roundTowardNegative,
    roundTowardPositive, roundTowardZero;

int push(int x) { return x + 1; }
int pop(int x) { return x - 1; }
int hide(int x) { return x * 2; }
int reveal(int x) { return x / 2; }

int main(void) {
  int x = __VERIFIER_nondet_int();
  assume(x > 0 && x < 100);

  action[0] = 1;
  asserts = datatype = hideable = is = measure = 1;
  preserves = pure = refines = revealed = uses = 1;
  RNA = RNE = RTN = RTP = RTZ = 1;
  roundNearestTiesToAway = roundNearestTiesToEven = roundTowardNegative = 1;
  roundTowardPositive = roundTowardZero = 1;

  int sum = action[0] + asserts + datatype + hideable + is + measure +
            preserves + pure + refines + revealed + uses + RNA + RNE + RTN +
            RTP + RTZ + roundNearestTiesToAway + roundNearestTiesToEven +
            roundTowardNegative + roundTowardPositive + roundTowardZero;

  assert(sum == 21);
  assert(reveal(hide(pop(push(x)))) == x + 1);
  return 0;
}
