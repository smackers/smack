#include "smack.h"
#include <assert.h>
#include <stdlib.h>

// @expect error

int *dll_create_generic(void (*insert_fnc)()) {
  int *dll = ((void *)0);
  insert_fnc(&dll);
  return dll;
}

void dll_insert_master(int **dll) {
  *dll = (int *)malloc(sizeof(int));
  **dll = 10;
}

int *dll_create_master(void) { return dll_create_generic(dll_insert_master); }

void inspect_base(int *dll) { assert(*dll != 10); }

void inspect_init(int *dll) { inspect_base(dll); }

int main(void) {
  int *dll = dll_create_master();
  inspect_init(dll);
  return 0;
}
