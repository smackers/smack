#include "smack.h"

// @expect verified
// @checkbpl grep -F 'call {:cexpr "(*pa)[2]"} boogie_si_record_i32'
// @checkbpl awk '/cexpr "pa\[2\]"/ { exit 1 }'
// @checkbpl awk '/cexpr "x\[1\]"/ { exit 1 }'
// @checkbpl grep -F 'call {:cexpr "m[1][2]"} boogie_si_record_i32'

// (*pa)[2] and pa[2] are different addresses, and a scalar's address is not an
// array; both used to be recorded under the wrong name.
int main(void) {
  int x = 1;
  int arr[4];
  int(*pa)[4] = &arr;
  int m[3][4];

  (*pa)[2] = 2;
  m[1][2] = 3;
  assert((*pa)[2] == 2 && m[1][2] == 3 && x == 1);
  return 0;
}
