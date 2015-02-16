//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACKREPFLATMEM_H
#define SMACKREPFLATMEM_H

#include "smack/SmackRep.h"

namespace smack {

using llvm::Regex;
using llvm::SmallVector;
using llvm::StringRef;
using namespace std;

class SmackRepFlatMem : public SmackRep {

  int bottom;

public:
  SmackRepFlatMem(DSAAliasAnalysis* aa) : SmackRep(aa), bottom(0) {}
};
}

#endif // SMACKREPFLATMEM_H

