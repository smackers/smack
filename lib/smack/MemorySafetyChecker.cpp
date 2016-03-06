//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/MemorySafetyChecker.h"
#include "smack/Naming.h"

#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Constants.h"
#include "llvm/Support/Debug.h"

namespace smack {
  using namespace llvm;

  bool MemorySafetyChecker::runOnModule(Module& m) {
    DataLayout* dataLayout = new DataLayout(&m);
    Function* verifierFunction = m.getFunction(Naming::VERIFIER_FUNCTION);
    assert(verifierFunction != NULL && "Couldn't find memory safety function");
    for (auto& F : m) {
      if(!Naming::isSmackName(F.getName())) {
        for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
          if(LoadInst* li = dyn_cast<LoadInst>(&*I)) {
            Value* pointer = li->getPointerOperand();
            Value* size = ConstantInt::get(IntegerType::get(F.getContext(), 64), dataLayout->getTypeSizeInBits(dyn_cast<PointerType>(li->getPointerOperand()->getType())->getPointerElementType()), false);
            Type *PtrTy = PointerType::getUnqual(IntegerType::getInt8Ty(F.getContext()));
            CastInst* castPointer = CastInst::Create(Instruction::BitCast, pointer, PtrTy, "", &*I);
            Value* args[] = {castPointer, size};
            CallInst::Create(verifierFunction, ArrayRef<Value*>(args, 2), "", &*I);
          } else if (StoreInst* si = dyn_cast<StoreInst>(&*I)) {
            Value* pointer = si->getPointerOperand();
            Value* size = ConstantInt::get(IntegerType::get(F.getContext(), 64), dataLayout->getTypeSizeInBits(si->getValueOperand()->getType()), false);
            Type *ptrTy = PointerType::getUnqual(IntegerType::getInt8Ty(F.getContext()));
            CastInst* castPointer = CastInst::Create(Instruction::BitCast, pointer, ptrTy, "", &*I);
            Value* args[] = {castPointer, size};
            CallInst::Create(verifierFunction, ArrayRef<Value*>(args, 2), "", &*I);
          }
        }
      }
    }
    return false;
  }

  // Pass ID variable
  char MemorySafetyChecker::ID = 0;
}
