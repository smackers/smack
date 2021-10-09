#include "smack.h"
#include <assert.h>

// @expect verified

typedef struct {
  int lock;
  int init;
} mutex_t;

mutex_t m_inode;
mutex_t m_busy;

void mutex_lock(mutex_t *lock) {
  assert(lock->init == 0);
  assert(lock->lock == 0);
  lock->init = 1;
  lock->lock = 2;
}

int main(void) {
  mutex_lock(&m_inode);
  mutex_lock(&m_busy);
  return 0;
}
