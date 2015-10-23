// Shows join.c fails when parent doesn't wait for child before x++ call

// @expect error

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
  x++;
  pthread_join(t, 0);
  assert(x == 3);
  return 0;
}
