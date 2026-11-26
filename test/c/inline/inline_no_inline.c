#include "smack.h"
#include <assert.h>

// @expect verified
// @flag --no-inline=keep
// @checkbpl grep "call .* := keep("
// @checkbpl awk '/call .*gone\(/ {n++} END {exit n != 0}'

int keep(int x) { return x + 1; }
int gone(int x) { return x + 2; }

int main(void) {
  assert(keep(1) == 2);
  assert(gone(1) == 3);
  return 0;
}
