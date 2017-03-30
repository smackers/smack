// Tests pthread_equal()
// @expect verified

#include <pthread.h>
#include <smack.h>

pthread_t worker;

void *t1(void *arg){ 
  __VERIFIER_assert(pthread_equal(pthread_self(),worker));
}

int main() {
  pthread_create(&worker,0,0,0);
  pthread_join(worker,0);
  __VERIFIER_assert(!pthread_equal(pthread_self(),worker));
}
