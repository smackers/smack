#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

typedef struct {
  int x;
  int y;
} point;

typedef struct {
  short data;
  point point1;
  int count;
  point point2;
  char status;
} element;

int main() {
  element elem;
  point p;

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

  p.x = 1000;
  p.y = 2000;
  elem.point1 = p;
  __SMACK_assert(elem.count == 2);
  __SMACK_assert(elem.data == 5);
  __SMACK_assert(elem.point2.x == 200);
  __SMACK_assert(p.x == 1000);
  __SMACK_assert(p.y == 2000);
  __SMACK_assert(elem.point1.x == 1000);
  __SMACK_assert(elem.point1.y == 2000);

  return 0;
}
