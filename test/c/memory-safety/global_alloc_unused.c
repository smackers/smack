#include "smack.h"

// @expect verified
// @checkbpl awk '/call \$galloc/ { found=1 } END { exit found }'

void loga(char *);

int main(void) {
  loga("aaa");
  return 0;
}
