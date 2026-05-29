//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef UTILS_INITIALIZEPASSES_H
#define UTILS_INITIALIZEPASSES_H

#include "llvm/InitializePasses.h"

namespace llvm {
void initializeDevirtualizePass(PassRegistry &Registry);
} // end namespace llvm

#endif // UTILS_INITIALIZEPASSES_H
