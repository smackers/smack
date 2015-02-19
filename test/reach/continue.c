#include "smack.h"

int main() {
  int a = 1;
  while(a != 5) {
    a++;
    continue;
    a = 0;
  }
  return a;
}
