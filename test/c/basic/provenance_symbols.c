#include "smack.h"
#include <assert.h>

// @expect verified
// @checkbpl grep '{:llvm.func "main"}'
// @checkbpl grep '{:llvm.inst "main:'
// @checkbpl grep '{:llvm.op "store"}'
// @checkbpl grep '{:lowering_kind "comparison"}'
// @checkbpl grep '{:source_var "x"}'
// @checkbpl grep '{:source_var "y"}'
// @checkbpl grep '{:source_expr "x >= y"}'
// @checkbpl grep '{:lowering_kind "zext_bool"}'
// @checkbpl grep '{:source_lhs "ok"}'
// @checkbpl grep '{:origin_condition "$sge.i32'
// @checkbpl grep '{:condition_id "check:'
// @checkbpl grep '{:source_op ">="}'
// @checkbpl grep '{:source_arg0 "x"}'
// @checkbpl grep '{:source_arg1 "y"}'
// @checkbpl grep '{:boogie_arg0 "$i'
// @checkbpl grep '{:boogie_arg1 "$i'
// @checkbpl grep '{:source_def "ok"}'
// @checkbpl grep '{:source_use "x"}'
// @checkbpl grep '{:source_use "y"}'
// @checkbpl grep '{:boogie_def "$i'
// @checkbpl grep '{:boogie_use "$i'
// @checkbpl grep '{:loop_role "header"}'
// @checkbpl grep '{:loop_id "main:'

volatile int g;

int check(int x, int y) {
  volatile int ok = x >= y;
  assert(ok);
  return ok;
}

int main(void) {
  int i = 0;
  while (i < 1) {
    i++;
  }
  g = check(2, 1);
  assert(g == 1);
  return 0;
}
