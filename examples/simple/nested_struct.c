#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

typedef struct {
  short data;
  struct {
    int x;
    int y;
  } point1;
  int count;
  struct {
    int x;
    int y;
  } point2;
  char status;
} element;

int main() {
  element elem;

  elem.count = 1;
  __SMACK_assert(elem.count == 1);

  elem.count = 2;
  __SMACK_assert(elem.count == 2);

  elem.point1.y = 100;
  __SMACK_assert(elem.count == 2);
  __SMACK_assert(elem.point1.y == 100);

  elem.data = 5;
  __SMACK_assert(elem.count == 2);
  __SMACK_assert(elem.point1.y == 100);
  __SMACK_assert(elem.data == 5);

  elem.point2.x = 200;
  __SMACK_assert(elem.count == 2);
  __SMACK_assert(elem.point1.y == 100);
  __SMACK_assert(elem.data == 5);
  __SMACK_assert(elem.point2.x == 200);

  return 0;
}
