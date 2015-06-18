// This file should have a race between the caller and callee threads
//  when executing the x++ instruction.

// @expect error

#include <pthread.h>

pthread_mutex_t lock = PTHREAD_MUTEX_INITIALIZER;

int x = 1;

void *t1(void *arg) {
  x++;
}

int main() {

  pthread_t t;

  pthread_create(&t, 0, t1, 0);
  x++;
  pthread_join(t, 0);
  assert(x == 3);
  

}
