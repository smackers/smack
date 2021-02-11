//===----------------------------------------------------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

//===----------------------------------------------------------------------===//
#include "smack/RemoveUndefPtrs.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

namespace smack {

char RemoveUndefPtrs::ID = 0;
static RegisterPass<RemoveUndefPtrs>
    X("remove-undef-ptrs", "Transform undef pointers into null pointers");

bool RemoveUndefPtrs::runOnFunction(Function &F) {
  bool changed = false;
  for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
    for (auto OI = I->op_begin(), OE = I->op_end(); OI != OE; ++OI) {
      Value *val = OI->get();
      if (auto *uv = dyn_cast<UndefValue>(val)) {
        if (PointerType *uvpt = dyn_cast<PointerType>(uv->getType())) {
          Value *replacement = ConstantPointerNull::get(uvpt);
          *OI = replacement;
          changed = true;
        }
      }
    }
  }

  return changed;
}

} // namespace smack
