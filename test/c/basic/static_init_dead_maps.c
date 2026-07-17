#include "smack.h"
#include <assert.h>

// @expect verified
// @checkbpl awk 'index($0, "123456789") { found=1 } END { exit found }'
// @checkbpl grep -q '123456788'

struct values {
  int used;
  int unused;
};

struct values data = {123456788, 123456789};

int main(void) {
  assert(data.used == 123456788);
  return 0;
}
