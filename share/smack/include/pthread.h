//
// Copyright (c) 2013 Zvonimir Rakamaric (zvonimir@cs.utah.edu),
//                    Michael Emmi (michael.emmi@gmail.com)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef PTHREAD_H
#define PTHREAD_H

#include "smack.h"

#define NULL (void*)0

/* Mutex types.  */
enum
{
  PTHREAD_MUTEX_TIMED_NP,
  PTHREAD_MUTEX_RECURSIVE_NP,
  PTHREAD_MUTEX_ERRORCHECK_NP,
  PTHREAD_MUTEX_ADAPTIVE_NP,
  PTHREAD_MUTEX_NORMAL = PTHREAD_MUTEX_TIMED_NP,
  PTHREAD_MUTEX_RECURSIVE = PTHREAD_MUTEX_RECURSIVE_NP,
  PTHREAD_MUTEX_ERRORCHECK = PTHREAD_MUTEX_ERRORCHECK_NP,
  PTHREAD_MUTEX_DEFAULT = PTHREAD_MUTEX_NORMAL,
  PTHREAD_MUTEX_FAST_NP = PTHREAD_MUTEX_TIMED_NP
};

typedef int pthread_t;
typedef int pthread_attr_t;

typedef struct{
  int prioceil, proto, pshared, type;
} pthread_mutexattr_t;

typedef struct{
  int lock, init;
  pthread_mutexattr_t attr;
} pthread_mutex_t;

typedef struct{
  int cond, init;
} pthread_cond_t;

typedef int pthread_condattr_t;


pthread_t pthread_self(void) {
  int ctid = __SMACK_nondet();
  __SMACK_code("call @ := corral_getThreadID();", ctid);
  return ctid;
}

int pthread_join(pthread_t __th, void **__thread_return) {
  void* tmp = (void*)(long)__SMACK_nondet();
  // Wait for the thread to terminate
  __SMACK_code("assume $pthreadStatus[@][0] == $pthread_stopped;", __th);
  // Get the thread's return value
  __SMACK_code("@ := $pthreadStatus[@][1];", tmp, __th);
  *__thread_return = tmp;
  return 0;
}

void pthread_exit(void *retval) {
  pthread_t tid = __SMACK_nondet();
  tid = pthread_self();
  __SMACK_code("assert $pthreadStatus[@][0] == $pthread_running;", tid);
  __SMACK_code("$pthreadStatus[@][1] := @;", tid, retval);
}

//model mutex:
//  0 = unlocked,
//  else = locked by thread with matching id

#define UNLOCKED 0
#define UNINITIALIZED 0
#define INITIALIZED 1
//  !!!!! ERROR HERE? - if mutex already initialized, behavior
//        of initialization should be undefined
#define PTHREAD_MUTEX_INITIALIZER {UNLOCKED, INITIALIZED}

int pthread_mutexattr_init(pthread_mutexattr_t *attr) {
  attr->type = PTHREAD_MUTEX_NORMAL;
}

int pthread_mutexattr_settype(pthread_mutexattr_t *attr, int type) {
  attr->type = type;
  return 0;
}

int pthread_mutex_init(pthread_mutex_t *mutex, const pthread_mutexattr_t *attr) {
  // Can't check for already initialized error, 
  //  since uninitialized values are nondet and could be INITIALIZED
  mutex->lock = UNLOCKED;
  mutex->init = INITIALIZED;
  if(attr == 0) {
    pthread_mutexattr_init(&mutex->attr);
  } else {
    mutex->attr.type = attr->type;
  }
  return 0;
}

int pthread_mutex_lock(pthread_mutex_t *__mutex) {
  int tid = (int)pthread_self();
  // Ensure mutex is initialized & hasn't already been locked by caller
  if(__mutex->attr.type==PTHREAD_MUTEX_NORMAL) {
    assert(__mutex->init == INITIALIZED);
    assert(__mutex->lock != tid);
  } else if(__mutex->attr.type==PTHREAD_MUTEX_ERRORCHECK) {
    if(__mutex->init != INITIALIZED)
      return 22;    // This is EINVAL
    if(__mutex->lock == tid)
      return 35;    // This is EDEADLK
  } else {
    // Other types not currently implemented
    assert(0);
  }
  __SMACK_code("call corral_atomic_begin();");
  // Wait for lock to become free
  assume(__mutex->lock == UNLOCKED);
  __mutex->lock = tid;
  __SMACK_code("call corral_atomic_end();");
  return 0;
}

int pthread_mutex_unlock(pthread_mutex_t *__mutex) {
  int tid = (int)pthread_self();
  // Ensure mutex is initialized & caller is current owner
  if(__mutex->attr.type==PTHREAD_MUTEX_NORMAL) {
    assert(__mutex->init == INITIALIZED);
    assert(__mutex->lock == tid);
  } else if(__mutex->attr.type==PTHREAD_MUTEX_ERRORCHECK) {
    if(__mutex->init != INITIALIZED)
      return 22;    // This is EINVAL
    if(__mutex->lock != tid) 
      return 1;     // This is EPERM
  } else {
    // Other types not currently implemented
    assert(0);
  }
  __SMACK_code("call corral_atomic_begin();");
  __mutex->lock = UNLOCKED;
  __SMACK_code("call corral_atomic_end();");
  return 0;
}

int pthread_mutex_destroy(pthread_mutex_t *__mutex) {
  // Make sure the lock is initialized, and unlocked
  assert(__mutex->init == INITIALIZED);
  assert(__mutex->lock == UNLOCKED);
  __SMACK_code("call corral_atomic_begin();");
  __mutex->init = UNINITIALIZED;
  __SMACK_code("call corral_atomic_end();");
  return 0;
}

int pthread_cond_init(pthread_cond_t *__cond, pthread_condattr_t *__condattr) {
  if(__condattr == 0) {
    __cond->cond = 0;
    __cond->init = INITIALIZED;
  } else {
    // Unimplemented
    assert(0);
  }
  return 0;  
}

int pthread_cond_wait(pthread_cond_t *__cond, pthread_mutex_t *__mutex) {
  // Ensure conditional var is initialized, and mutex is locked properly
  assert(__cond->init == INITIALIZED);
  assert((int)pthread_self() == __mutex->lock);
  
}

void __call_wrapper(pthread_t *__restrict __newthread, void *(*__start_routine) (void *), void *__restrict __arg) {

  int ctid = __SMACK_nondet();
  __SMACK_code("call @ := corral_getThreadID();", ctid);
  assume(ctid == *__newthread);
  
  
  __SMACK_code("$pthreadStatus[@][0] := $pthread_waiting;", *__newthread);

  __SMACK_code("$pthreadStatus[@][0] := $pthread_running;", *__newthread);
  __start_routine(__arg);
  __SMACK_code("$pthreadStatus[@][0] := $pthread_stopped;", *__newthread);
}

int pthread_create(pthread_t *__restrict __newthread, __const pthread_attr_t *__restrict __attr, void *(*__start_routine) (void *), void *__restrict __arg) {

    //Declare corral primitive procedures
    __SMACK_top_decl("procedure corral_getThreadID() returns (x:int);");
    __SMACK_top_decl("procedure corral_getChildThreadID() returns (x:int);");
    __SMACK_top_decl("procedure corral_atomic_begin();");
    __SMACK_top_decl("procedure corral_atomic_end();");
    //Array for tracking pthreads
    __SMACK_top_decl("//dim0=tid, dim1= 0 for status, 1 for return");
    __SMACK_top_decl("var $pthreadStatus: [int][int]int;");
    __SMACK_top_decl("const unique $pthread_uninitialized: int;");
    __SMACK_top_decl("const unique $pthread_initialized: int;");
    __SMACK_top_decl("const unique $pthread_waiting: int;");
    __SMACK_top_decl("const unique $pthread_running: int;");
    __SMACK_top_decl("const unique $pthread_stopped: int;");
    //__pthreads_init();

  //Mystery smack_nondet for procedure calls from __SMACK_code??
  int x = __SMACK_nondet();
  pthread_t tmp = __SMACK_nondet();
  assume(x == 0);
  if(x) __call_wrapper(__newthread, __start_routine, __arg);
  __SMACK_code("async call @(@, @, @);", __call_wrapper, __newthread, __start_routine, __arg);
  __SMACK_code("call @ := corral_getChildThreadID();", tmp);
  *__newthread = tmp;

  return 0;
}

#endif // PTHREAD_H
