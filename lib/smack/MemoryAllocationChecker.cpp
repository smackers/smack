//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/MemoryAllocationChecker.h"
#include "smack/Naming.h"

#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Constants.h"
#include "llvm/Support/Debug.h"

namespace smack {
  using namespace llvm;

  const char* VERIFIER_FUNCTION = "__SMACK_check_memory_access";

  bool MemoryAllocationChecker::runOnModule(Module& m) {
    DataLayout* dataLayout = new DataLayout(&m);
    Function* verifierFunction;
    for(auto& f:m) {
      if(f.getName() == VERIFIER_FUNCTION) {
        verifierFunction = &f;
        break;
      }
    }
    for (auto& F : m) {
      if(!Naming::isSmackName(F.getName())) {
        for (auto& B : F) {
          for (auto& I : B) {
            if(LoadInst* li = dyn_cast<LoadInst>(&I)) {
              Value* pointer = li->getPointerOperand();
              Value* size = ConstantInt::get(IntegerType::get(F.getContext(), 64), dataLayout->getTypeSizeInBits(dyn_cast<PointerType>(li->getPointerOperand()->getType())->getPointerElementType()), false);
              Type *PtrTy = PointerType::getUnqual(IntegerType::getInt8Ty(F.getContext()));
              CastInst* castPointer = CastInst::Create(Instruction::BitCast, pointer, PtrTy, "", &I);
              Value* args[] = {castPointer, size};
              CallInst::Create(verifierFunction, ArrayRef<Value*>(args, 2), "", &I);
            } else if (StoreInst* si = dyn_cast<StoreInst>(&I)) {
              Value* pointer = si->getPointerOperand();
              Value* size = ConstantInt::get(IntegerType::get(F.getContext(), 64), dataLayout->getTypeSizeInBits(si->getValueOperand()->getType()), false);
              Type *PtrTy = PointerType::getUnqual(IntegerType::getInt8Ty(F.getContext()));
              CastInst* castPointer = CastInst::Create(Instruction::BitCast, pointer, PtrTy, "", &I);
              Value* args[] = {castPointer, size};
              CallInst::Create(verifierFunction, ArrayRef<Value*>(args, 2), "", &I);
            }
          }
        }
      }
    }
    return false;
  }

  // Pass ID variable
  char MemoryAllocationChecker::ID = 0;
}
