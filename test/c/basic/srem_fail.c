#include "smack.h"
#include <assert.h>

// @expect error
// @checkbpl grep ':= \$srem'

int main(void) {
  int x;
  x = 62951;
  assert(x % (-37) == 14);
  x = 81165;
  assert(x % 34 == 7);
  x = -74602;
  assert(x % 47 == (-13));
  x = 82682;
  assert(x % (-28) == 26);
  x = 26476;
  assert(x % (-19) == 9);
  x = -80492;
  assert(x % 5 == (-2));
  x = -44299;
  assert(x % (-31) == 0);
  x = 9380;
  assert(x % 50 == 30);
  x = 91508;
  assert(x % 50 == 8);
  x = 92985;
  assert(x % 47 == 19);
  x = -68477;
  assert(x % 23 == (-6));
  x = 94126;
  assert(x % 49 == 46);
  x = 91440;
  assert(x % (-39) == 24);
  x = -2922;
  assert(x % 30 != (-12));
  x = 60062;
  assert(x % (-21) == 2);
  x = -71622;
  assert(x % (-50) == (-22));
  x = -15645;
  assert(x % (-39) == (-6));
  x = 83154;
  assert(x % 14 == 8);
  x = 58447;
  assert(x % 38 == 3);
  return 0;
}
