//
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "smack/PromoteMemcpy.h"
#include "llvm/IR/Module.h"

namespace smack {

using namespace llvm;

bool PromoteMemcpy::tryPromote(MemCpyInst *I,
                               std::vector<Instruction *> &instToErase) {
  if (!llvm::isa<ConstantInt>(I->getLength()))
    return false;

  auto srcPtr = I->getSource();
  auto dstPtr = I->getDest();
  auto srcTy = srcPtr->getType();
  auto dstTy = dstPtr->getType();

  if (srcTy != dstTy)
    return false;

  auto srcElemTy = llvm::cast<PointerType>(srcTy)->getPointerElementType();
  // We only rewrite these two types of pointer arguments
  if (!srcElemTy->isStructTy() && !srcElemTy->isArrayTy())
    return false;

  auto size = llvm::cast<ConstantInt>(I->getLength())->getLimitedValue();
  auto elemSize = DL->getTypeStoreSize(srcElemTy);
  if (size != elemSize)
    return false;

  // Finally the real work: turn memcpy into load-then-store
  auto si = new StoreInst(new LoadInst(srcElemTy, srcPtr, "", I), dstPtr, I);
  I->replaceAllUsesWith(si);
  instToErase.push_back(I);
  return true;
}

bool PromoteMemcpy::runOnFunction(Function &F) {
  bool ret = false;
  DL = &F.getParent()->getDataLayout();
  std::vector<Instruction *> instToErase;

  for (auto &B : F)
    for (auto &I : B)
      if (auto MI = dyn_cast<MemCpyInst>(&I))
        ret |= tryPromote(MI, instToErase);

  for (auto I : instToErase)
    I->eraseFromParent();
  return ret;
}

// Pass ID variable
char PromoteMemcpy::ID = 0;

StringRef PromoteMemcpy::getPassName() const {
  return "Rewrite array/struct memcpy into assignments";
}

} // namespace smack
