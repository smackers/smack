// Tests that uninitialized mutex fails on use

// @expect error

#include <pthread.h>
#include <smack.h>

int main() {
  pthread_mutex_t lock;
  pthread_mutex_lock(&lock);
  pthread_mutex_unlock(&lock);
  return 0;
}
