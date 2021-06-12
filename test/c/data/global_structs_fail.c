#include "smack.h"
#include <assert.h>

// @expect error

typedef struct {
  int lock;
  int init;
} mutex_t;

mutex_t m_inode;
mutex_t m_busy;

void mutex_lock(mutex_t *lock) {
  lock->init = 1;
  lock->lock = 2;
}

int main(void) {
  mutex_lock(&m_inode);
  mutex_lock(&m_busy);
  assert(m_inode.init == 0 || m_inode.lock == 0 || m_busy.init == 0 ||
         m_busy.lock == 0);
  return 0;
}
