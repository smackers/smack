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

int main(void) {
  element elem;

  elem.count = 1;
  elem.count = 2;
  elem.point1.y = 100;
  elem.data = 5;
  elem.point2.x = 200;

  assert(elem.count != 2 || elem.point1.y != 100 || elem.data != 5 || elem.point2.x != 200);

  return 0;
}

