/* https://graphics.stanford.edu/~seander/bithacks.html#InterleaveTableObvious
 */
#include "smack.h"
#include <assert.h>

// @flag --loop-limit=17
// @flag --unroll=17
// @expect error

int main() {
  /* Interleave bits of x and y, so that all of the */
  /* bits of x are in the even positions and y in the odd; */
  unsigned short x = __VERIFIER_nondet_unsigned_short();
  unsigned short y = __VERIFIER_nondet_unsigned_short();

  unsigned int xx;
  unsigned int yy;
  unsigned int zz;

  unsigned int z = 0; /* z gets the resulting Morton Number. */
  unsigned int i = 0;

  while (i < sizeof(x) * 8) {
    z |= ((x & (1U << i)) << i) | ((y & (1U << i)) << (i + 1));
    i += 1U;
  }

  xx = x;
  yy = y;

  xx = (xx | (xx << 8u)) & 16711935U;   /* 0x00FF00FF */
  xx = (xx | (xx << 4u)) & 252645135U;  /* 0x0F0F0F0F */
  xx = (xx | (xx << 2u)) & 858993459U;  /* 0x33333333 */
  xx = (xx | (xx << 1u)) & 1431655765U; /* 0x55555555 */

  yy = (yy | (yy << 8u)) & 16711935U;   /* 0x00FF00FF */
  yy = (yy | (yy << 4u)) & 252645135U;  /* 0x0F0F0F0F */
  yy = (yy | (yy << 2u)) & 858993459U;  /* 0x33333333 */
  yy = (yy | (yy << 1u)) & 1431655765U; /* 0x55555555 */

  zz = xx | (yy << 2U);

  assert(z == zz);
}
