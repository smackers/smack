#include "smack.h"

int func() {
  return 1;
}

int func2() {
  return func();
}

int main() {
  int a;
  a = 1;
  return a;
}
