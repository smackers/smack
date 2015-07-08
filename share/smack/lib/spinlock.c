#include "spinlock.h"

void spin_lock(spinlock_t *__lock) {
  int ctid = __VERIFIER_nondet_int();
  __SMACK_code("call @ := corral_getThreadID();", ctid);
  assert(ctid != (unsigned int)(*__lock));
  __SMACK_code("call corral_atomic_begin();");
  assume(*__lock == SPIN_LOCK_UNLOCKED);
  *__lock = (spinlock_t)ctid;
  __SMACK_code("call corral_atomic_end();");
}

void spin_unlock(spinlock_t *__lock) {
  int ctid = __VERIFIER_nondet_int();
  __SMACK_code("call @ := corral_getThreadID();", ctid);
  assert((unsigned int)ctid == (unsigned int)(*__lock));
  __SMACK_code("call corral_atomic_begin();");
 *__lock = SPIN_LOCK_UNLOCKED;
  __SMACK_code("call corral_atomic_end();");
}
