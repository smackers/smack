#ifndef SMACK_H_
#define SMACK_H_

#include <stdbool.h>

void __SMACK_code(const char *fmt, ...);

void __SMACK_assert(bool v) {
  __SMACK_code("assert {@} != 0;", v);
}

void __SMACK_assume(bool v) {
  __SMACK_code("assume {@} != 0;", v);
}

// void __SMACK_record_int(int i) {
//   __SMACK_code("call boogie_si_record_int(@);", i);
// }

int __SMACK_nondet() {
  static int XXX;
  int x = XXX;
  __SMACK_code("havoc @;", x);
  return x;
}

#endif /*SMACK_H_*/
