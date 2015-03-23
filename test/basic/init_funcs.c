#include "smack.h"

// @expect verified
// @flag --unroll=1

void __SMACK_INIT(defineProcessStates) {
  __SMACK_top_decl("const unique $process_uninitialized: int;");
  __SMACK_top_decl("const unique $process_initialized: int;");
  __SMACK_top_decl("var $processInitStatus: [int]int;");
  __SMACK_top_decl("var $randomBoogieVar: int;");
}

void __SMACK_INIT(initializeProcessStates) {
  __SMACK_code("assume (forall x:int :: $processInitStatus[x] == $process_uninitialized);");
  __SMACK_code("$randomBoogieVar := 3;");
}

void main() {
  __SMACK_code("assert($randomBoogieVar == 3);");
  __SMACK_code("assert($processInitStatus[10] == $process_uninitialized);");
}
