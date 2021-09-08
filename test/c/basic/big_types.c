#include "smack.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

// @expect verified

typedef struct {
  unsigned a : 32;
  unsigned b : 32;
  unsigned c : 32;
} S1;

typedef struct {
  unsigned a : 32;
  unsigned b : 32;
  unsigned c : 32;
  unsigned d : 32;
} S2;

int main(void) {
  S1 s1;
  S2 s2;
  s1.a = 1;
  s2.a = 0;
  assert(1);
}
