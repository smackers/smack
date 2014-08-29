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

//int pthread_id_src = 0;

/* Thread identifiers */
typedef int pthread_t;

int pthread_initializer = 0;



//typedef struct pthread_t {
//  int status;
//  int smack_id;
//  int pthread_id;
//  int 
//} pthread_t;

typedef union {
  char __size[__SIZEOF_PTHREAD_ATTR_T];
  long int __align;
} pthread_attr_t;

//!!!!!!TEST

void __SMACK_atomic_begin() {
  __SMACK_code("call corral_atomic_begin();");
}

void __SMACK_atomic_end() {
  __SMACK_code("call corral_atomic_end();");
}

pthread_t pthread_self(void) {
  //Added these next two lines to get smack to translate how I wanted
  pthread_t tid = __SMACK_nondet();
  __SMACK_code("call @ := corral_getThreadID();", tid);
  __SMACK_code("assert @ != @;", tid, 0);
  return tid;
}

int pthread_join(pthread_t __th, void **__thread_return) {
  //__SMACK_code("assume $threadStatus[@][0] == $pthread_stopped;", __th);
  __SMACK_code("assume $threadStatus[@] == $pthread_stopped;", __th);
  //__SMACK_code("@ := $threadStatus[@][1];", *__thread_return, __th);
  return 0;
}

//model mutex:
//  0 = unlocked,
//  else = locked by thread with matching id

typedef int pthread_mutex_t;
#define UNLOCKED 0
#define PTHREAD_MUTEX_INITIALIZER UNLOCKED

int pthread_mutex_lock(pthread_mutex_t *__mutex) {

  int tid = (int)pthread_self();

  int lockStatus = (int)(*__mutex);

  __SMACK_code("call corral_atomic_begin();");
  __SMACK_code("assume @ == @;", lockStatus, (int)(*__mutex));
  __SMACK_code("assert @ != @;", tid, lockStatus);
  __SMACK_code("assume @ == @;", lockStatus, UNLOCKED);
  *__mutex = (pthread_mutex_t)tid;
  __SMACK_code("call corral_atomic_end();");
  return 0;
}

int pthread_mutex_unlock(pthread_mutex_t *__mutex) {
  int tid = (int)pthread_self();
  int lockStatus = (int)*__mutex;

  __SMACK_code("call corral_atomic_begin();");
  __SMACK_code("assert @ == @;", lockStatus, (int)(*__mutex));
  __SMACK_code("assume @ == @;", tid, lockStatus);
  *__mutex = UNLOCKED;
  __SMACK_code("call corral_atomic_end();");
  return 0;
}


//!!!!!!ENDTEST

void __pthreads_init() {
  static unsigned int inserted = 0;
  if (!inserted) {
    inserted = 1;
    __SMACK_top_decl("procedure corral_getThreadID() returns (x:int);");
    __SMACK_top_decl("procedure corral_atomic_begin();");
    __SMACK_top_decl("procedure corral_atomic_end();");
    __SMACK_top_decl("//dim0=tid, dim1= 0 for status, 1 for return");
    //__SMACK_top_decl("var $threadStatus: [int][int]int;");
    __SMACK_top_decl("var $threadStatus: [int]int;");
    __SMACK_top_decl("const unique $pthread_uninitialized: int;");
    __SMACK_top_decl("const unique $pthread_waiting: int;");
    __SMACK_top_decl("const unique $pthread_running: int;");
    __SMACK_top_decl("const unique $pthread_stopped: int;");
  }
}

void __call_wrapper(pthread_t *__restrict __newthread, void *(*__start_routine) (void *), void *__restrict __arg) {
  //__SMACK_atomic_begin();
  __SMACK_code("assert $threadStatus[@] == $pthread_uninitialized;", __newthread);
  
  __SMACK_code("$threadStatus[@] := $pthread_waiting;", __newthread);
  //__SMACK_code("$threadStatus[@][0] := $pthread_waiting;", *__newthread);

  //__SMACK_code("call corral_atomic_end();");
  //__SMACK_code("$threadStatus[@][0] := $pthread_running;", *__newthread);
  __SMACK_code("$threadStatus[@] := $pthread_running;", __newthread);
  //int* retpt = (int*)__start_routine(__arg);
  __start_routine(__arg);
  //__SMACK_atomic_begin();
  //int ret = (int)(*retpt);
  //__SMACK_code("$threadStatus[@][1] := @;", *__newthread, ret);
  //__SMACK_code("$threadStatus[@][0] := $pthread_stopped;", *__newthread);
  __SMACK_code("$threadStatus[@] := $pthread_stopped;", __newthread);
  //__SMACK_atomic_end();
}

int pthread_create(pthread_t *__restrict __newthread, __const pthread_attr_t *__restrict __attr, void *(*__start_routine) (void *), void *__restrict __arg) {
  __pthreads_init();
  // What are the next four lines for???  (by monty)
  //int x = __SMACK_nondet();
  //__SMACK_assume(x == 0);
  //if (x)
  //__call_wrapper(__newthread, __start_routine, __arg);
  *__newthread = ++pthread_initializer;
  __SMACK_code("async call @(@, @, @);", __call_wrapper, __newthread, __start_routine, __arg);

  return 0;
}

#endif // PTHREAD_H
