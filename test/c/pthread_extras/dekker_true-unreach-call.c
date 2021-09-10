/* Testcase from Threader's distribution. For details see:
   http://www.model.in.tum.de/~popeea/research/threader
*/

#include "pthread.h"
#include "smack.h"
#include <assert.h>

// @expect verified
// @flag --unroll=4

int flag1 = 0, flag2 = 0; // boolean flags
int turn; // integer variable to hold the ID of the thread whose turn is it
int x;    // boolean variable to test mutual exclusion

void *thr1(void *arg) {
  flag1 = 1;
  while (flag2 >= 1) {
    if (turn != 0) {
      flag1 = 0;
      while (turn != 0) {
      };
      flag1 = 1;
    }
  }
  // begin: critical section
  x = 0;
  assert(x <= 0);
  // end: critical section
  turn = 1;
  flag1 = 0;
}

void *thr2(void *arg) {
  flag2 = 1;
  while (flag1 >= 1) {
    if (turn != 1) {
      flag2 = 0;
      while (turn != 1) {
      };
      flag2 = 1;
    }
  }
  // begin: critical section
  x = 1;
  assert(x >= 1);
  // end: critical section
  turn = 1;
  flag2 = 0;
}

int main() {
  pthread_t t1, t2;
  assume(0 <= turn && turn <= 1);
  pthread_create(&t1, 0, thr1, 0);
  pthread_create(&t2, 0, thr2, 0);
  pthread_join(t1, 0);
  pthread_join(t2, 0);
  return 0;
}
