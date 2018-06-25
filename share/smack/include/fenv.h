// This file is distributed under the MIT License. See LICENSE for details.
//

#ifndef FENV_H
#define FENV_H

#define FE_TONEARESTEVEN 1
#define FE_TONEARESTAWAY 2
#define FE_UPWARD 3
#define FE_DOWNWARD 4
#define FE_TOWARDZERO 5

int fegetround(void);
int fesetround(int);

#endif
