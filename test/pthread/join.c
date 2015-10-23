// Shows pthread_join effectively blocks until child thread done

// @expect verified

#include <pthread.h>
#include <smack.h>

int x = 1;

void *t1(void *arg) {
  x++;
  pthread_exit(0);
}

int main() {

  pthread_t t;

  pthread_create(&t, 0, t1, 0);
  pthread_join(t, 0);
  x++;
  assert(x == 3);
  return 0;
}
