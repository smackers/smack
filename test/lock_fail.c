#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

#define UNLOCKED 0
#define LOCKED 1

typedef struct {
  int status;
  int locked;
} lock;

lock main_lock;
lock global_lock;

void acquire_lock(lock *l) {
  assert(l->locked == UNLOCKED);
  l->locked = LOCKED;
}

void release_lock(lock *l) {
  assert(l->locked == LOCKED);
  l->locked = UNLOCKED;
}

int main(void) {
  main_lock.locked = UNLOCKED;
  global_lock.locked = UNLOCKED;
  acquire_lock(&main_lock);
  acquire_lock(&global_lock);
  release_lock(&main_lock);
  acquire_lock(&global_lock);
  return 0;
}

