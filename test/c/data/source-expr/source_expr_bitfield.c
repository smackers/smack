#include "smack.h"

// @expect verified
// @checkbpl grep -F 'call {:cexpr "b->after"} boogie_si_record_i32'
// @checkbpl awk '/cexpr "b->f1"/ { exit 1 }'
// @checkbpl awk '/cexpr "b->f2"/ { exit 1 }'

// Two bitfields share one LLVM storage unit, so the third member sits at LLVM
// field index 1 while it is the third DW_TAG_member. Naming it by ordinal
// position reported it as f2.
struct bits {
  unsigned f1 : 3;
  unsigned f2 : 5;
  int after;
};

int main(void) {
  struct bits s;
  struct bits *b = &s;
  b->after = 42;
  assert(b->after == 42);
  return 0;
}
