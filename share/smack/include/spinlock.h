//
// Copyright (c) 2013 Zvonimir Rakamaric (zvonimir@cs.utah.edu),
//                    Michael Emmi (michael.emmi@gmail.com)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SPINLOCK_H
#define SPINLOCK_H


// Begin:: A bunch of stuff to support multiple methods to init locks:
typedef unsigned int spinlock_t;

#define __SPIN_LOCK_UNLOCKED()  (spinlock_t)0

#define SPIN_LOCK_UNLOCKED      __SPIN_LOCK_UNLOCKED()
#define DEFINE_SPINLOCK(x)      spinlock_t x = __SPIN_LOCK_UNLOCKED()

#define spin_lock_init(lock)                                   \
        do { *(lock) = SPIN_LOCK_UNLOCKED; } while (0)
// End::  a bunch of stuff to init locks

//model spinlock:
//  0 = unlocked,
//  else = locked by thread with matching id

void spin_lock(spinlock_t *__lock);

void spin_unlock(spinlock_t *__lock);

#endif // SPINLOCK_H
