#include "smack.h"
#include <assert.h>
#include <pthread.h>

// Tests that uninitialized mutex fails on use
// @expect error

int main(void) {
  pthread_mutex_t lock;
  pthread_mutex_lock(&lock);
  pthread_mutex_unlock(&lock);
  return 0;
}
