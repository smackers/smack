
// @expect verified

#include <pthread.h>
#include <smack.h>

int x = 1;

void *t1(void *arg) {
  x++;
  if(x == 2)
    pthread_exit((void*)5);

  // Should never run this line, since called pthread_exit
  pthread_exit((void*)6);
}

int main() {

  pthread_t t;

  int a;
  void *ret;

  pthread_create(&t, 0, t1, 0);
  pthread_join(t, &ret);
  assert((int)ret == 5);
  return 0;
}
