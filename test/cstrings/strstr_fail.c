
#include <string.h>
#include "smack.h"

// @flag unroll=5
// @expect error

int main() {
  char *large = "lmno";
  char *small = "xy";

  char *firstOccurrenceOfXY = strstr(large,small);

  assert(firstOccurrenceOfXY != 0);

  return 0;
}
