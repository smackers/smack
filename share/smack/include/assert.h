//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef ASSERT_H
#define ASSERT_H
#include <smack.h>

#define assert(EX)                                                             \
  do {                                                                         \
    if (!(EX))                                                                 \
      __VERIFIER_assert(0);                                                    \
  } while (0)
#define assume(EX)                                                             \
  do {                                                                         \
    if (!(EX))                                                                 \
      __VERIFIER_assume(0);                                                    \
  } while (0)

#endif
