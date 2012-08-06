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

void __SMACK_anno_acquire_lock(lock *l) {
  __SMACK_requires(l->locked == UNLOCKED);
  __SMACK_ensures(l->locked == LOCKED);
  __SMACK_modifies(__SMACK_set(&l->locked));
}
void acquire_lock(lock *l) {
  __SMACK_anno_acquire_lock(l);
  l->locked = LOCKED;
}

void __SMACK_anno_release_lock(lock *l) {
  __SMACK_requires(l->locked == LOCKED);
  __SMACK_ensures(l->locked == UNLOCKED);
  __SMACK_modifies(__SMACK_set(&l->locked));
}
void release_lock(lock *l) {
  __SMACK_anno_release_lock(l);
  l->locked = UNLOCKED;
}

void __SMACK_anno_main(void) {
  __SMACK_requires(__SMACK_OBJNOALIAS(&main_lock, &global_lock));
  __SMACK_modifies(__SMACK_union(__SMACK_set(&main_lock.locked),
                                 __SMACK_set(&global_lock.locked)));
}
int main(void) {
  main_lock.locked = UNLOCKED;
  global_lock.locked = UNLOCKED;
  acquire_lock(&main_lock);
  release_lock(&main_lock);
  acquire_lock(&global_lock);
  release_lock(&global_lock);
  return 0;
}

