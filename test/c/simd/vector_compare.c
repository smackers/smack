#include "smack.h"
#include <assert.h>

// @expect verified
// @checkbpl grep "function \$eq.vec.2xi32.*returns (vec.2xi1) { mk.vec.2xi1"
// @checkbpl grep "function \$sext.vec.2xi1.vec.2xi32"

typedef int v2i __attribute__((vector_size(8)));

int main(void) {
  v2i x = {1, 2};
  v2i y = {1, 3};
  v2i z = x == y;
  assert(z[0] != 0);
  assert(z[1] == 0);
  return 0;
}
