//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include <errno.h>

static int errno_global;
int *__errno_location(void) { return &errno_global; }
