#include "smack.h"

// @expect verified
// @checkbpl grep -F 'call {:cexpr "c->c1"} boogie_si_record_i32'
// @checkbpl awk '/cexpr "[as.>-]*a1"/ { exit 1 }'

// struct A and struct C have different layouts, so this really is a bitcast
// between unrelated pointee types. Carrying struct A's debug type across it
// would let the GEP below resolve field 1 against struct A and record the
// store under a member of an object that is not being written.
struct A {
  int a0;
  int a1;
};
struct C {
  char c0;
  int c1;
};

int main(void) {
  struct A s;
  struct A *a = &s;
  struct C *c = (struct C *)a;
  c->c1 = 7;
  assert(c->c1 == 7);
  return 0;
}
