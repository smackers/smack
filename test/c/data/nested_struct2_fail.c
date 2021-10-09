#include "smack.h"
#include <stdio.h>
#include <stdlib.h>

// @expect error

typedef struct {
  int x;
  int y;
} point;

typedef struct {
  short data;
  point *point1;
  int count;
  point point2;
  char status;
} element;

int main(void) {
  element elem;
  point p;

  elem.count = 1;
  elem.count = 2;
  elem.point1 = &p;
  elem.point1->y = 100;
  elem.data = 5;
  elem.point2.x = 200;
  p.x = 1000;
  p.y = 2000;

  assert(elem.count != 2 || elem.data != 5 || elem.point2.x != 200 ||
         p.x != 1000 || p.y != 2000 || elem.point1->x != 1000 ||
         elem.point1->y != 2000);

  return 0;
}
