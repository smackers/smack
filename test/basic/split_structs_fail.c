#include "smack.h"

//There exists a load/store instruction of type {i64, i32}
//in function main, respectively.

// @flag --split-structs
// @expect error 

typedef struct {
  int x;
  int y;
  int z;
} S;

S foo() {
  S s;
  s.x = 1;
  s.y = 2;
  s.z = 3;
  return s;
}

int main() {
  S s = foo();
  assert(s.z == 2);
  return 0;
}
