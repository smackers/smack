#include "smack.h"

// @expect error

// This file provides an example of the intended use for init_funcs
// The functionality of both __SMACK_INIT calls would be implemented
// in a header file somewhere.

// The idea behind this example is to model the OS's tracking of processes
// statuses, for building a model of the system fork call.

// See share/smack/include/pthread.h for an actual, live example.


// In normal use, these would be listed somewhere in the header file
// (it does not need to be in a __SMACK_INIT call)
__SMACK_INIT(defineProcessStates) {
  __SMACK_top_decl("const unique $process_uninitialized: int;");
  __SMACK_top_decl("const unique $process_initialized: int;");
  __SMACK_top_decl("const unique $process_running: int;");
  __SMACK_top_decl("const unique $process_waiting: int;");
  __SMACK_top_decl("const unique $process_stopped: int;");
  __SMACK_top_decl("var $processStatus: [int]int;");
}

// This is the one that would need to be in a __SMACK_INIT call,
// since this assumption is not just a declaration/definition.
// This definition would also be listed in the model's header file.
__SMACK_INIT(initializeProcessStates) {
  __SMACK_code("assume (forall x:int :: $processStatus[x] == $process_uninitialized);");
}

void main() {
  int idx = __VERIFIER_nondet_int();
  __SMACK_code("assert($processStatus[@] != $process_uninitialized);", idx);
}

