//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef FENV_H
#define FENV_H

#define FE_TONEAREST 0
#define FE_DOWNWARD 0x400
#define FE_UPWARD 0x800
#define FE_TOWARDZERO 0xc00

int fegetround(void);
int fesetround(int);

#endif
