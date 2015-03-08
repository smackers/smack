//
// Copyright (c) 2013 Zvonimir Rakamaric (zvonimir@cs.utah.edu),
//                    Michael Emmi (michael.emmi@gmail.com)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef PTHREAD_H
#define PTHREAD_H


#include "smack.h"

#define NULL (void*)0

/* Determine the wordsize from the preprocessor defines.  */

#if defined __x86_64__
# define __WORDSIZE	64
#else
# define __WORDSIZE	32
#endif

#if __WORDSIZE == 64
# define __SIZEOF_PTHREAD_ATTR_T 56
#else
# define __SIZEOF_PTHREAD_ATTR_T 36
#endif

/* Thread identifiers */
typedef int pthread_t;

int pthread_initializer = 0;

typedef union {
  char __size[__SIZEOF_PTHREAD_ATTR_T];
  long int __align;
} pthread_attr_t;

pthread_t pthread_self(void) {
  int ctid = __SMACK_nondet();
  __SMACK_code("call @ := corral_getThreadID();", ctid);
  return ctid;
}

int pthread_join(pthread_t __th, void **__thread_return) {
  void* tmp = (void*)(long)__SMACK_nondet();
  __SMACK_code("assume $pthreadStatus[@][0] == $pthread_stopped;", __th);
  __SMACK_code("@ := $pthreadStatus[@][1];", tmp, __th);
  *__thread_return = tmp;
  return 0;
}

void pthread_exit(void *retval)
{
  pthread_t tid = __SMACK_nondet();
  tid = pthread_self();
  __SMACK_code("assert $pthreadStatus[@][0] == $pthread_running;", tid);
  __SMACK_code("$pthreadStatus[@][1] := @;", tid, retval);
  //__SMACK_code("assume false;");
}

//model mutex:
//  0 = unlocked,
//  else = locked by thread with matching id

typedef int pthread_mutex_t;
typedef int pthread_mutexattr_t;
#define UNLOCKED 0
#define PTHREAD_MUTEX_INITIALIZER UNLOCKED

int pthread_mutex_init(pthread_mutex_t *mutex, const pthread_mutexattr_t *attr) 
{
  if(attr == 0) {
    *mutex = UNLOCKED;
  } else {
    // Unimplemented
    assert(0);
  }
  return 0;
}

int pthread_mutex_lock(pthread_mutex_t *__mutex) {
  __SMACK_code("call corral_atomic_begin();");
  int tid = (int)pthread_self();
  __SMACK_code("assert @ != @;", tid, (int)(*__mutex));
  __SMACK_code("assume @ == @;", (int)(*__mutex), UNLOCKED);
  *__mutex = (pthread_mutex_t)tid;
  __SMACK_code("call corral_atomic_end();");
  return 0;
}

int pthread_mutex_unlock(pthread_mutex_t *__mutex) {
  __SMACK_code("call corral_atomic_begin();");
  int tid = (int)pthread_self();
  __SMACK_code("assert @ == @;", tid, (int)(*__mutex));
  *__mutex = UNLOCKED;
  __SMACK_code("call corral_atomic_end();");
  return 0;
}


//!!!!!!ENDTEST

/*void __pthreads_init() {
  __SMACK_code("call corral_atomic_begin();");
  static unsigned int inserted = 0;
  if (!inserted) {
    inserted = 1;
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
    
  __SMACK_code("call corral_atomic_end();");
  }
  }*/

void __call_wrapper(pthread_t *__restrict __newthread, void *(*__start_routine) (void *), void *__restrict __arg) {

  int ctid = __SMACK_nondet();
  __SMACK_code("call @ := corral_getThreadID();", ctid);
  __SMACK_code("assume @ == @;", ctid, *__newthread);
  
  
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
