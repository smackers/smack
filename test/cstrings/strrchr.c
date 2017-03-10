
#include <string.h>
#include "smack.h"

// @flag --unroll=5
// @expect verified

int main() {
  char *website = "a..b";

  char *dotCom = strrchr(website,'.');

  assert(strcmp(dotCom,".b") == 0);

  return 0;
}
