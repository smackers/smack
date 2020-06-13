//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef INITIALIZEPASSES_H
#define INITIALIZEPASSES_H

#include "llvm/InitializePasses.h"

namespace llvm {
void initializeDSAWrapperPass(PassRegistry &Registry);
void initializeCodifyStaticInitsPass(PassRegistry &Registry);
} // end namespace llvm

#endif // INITIALIZEPASSES_H
