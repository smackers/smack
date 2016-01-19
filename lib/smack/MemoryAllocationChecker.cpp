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
    //printf("in the module\n");
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
        F.print(errs());
        for (auto& B : F) {
          for (auto& I : B) {
            printf("\n");
            if(LoadInst* li = dyn_cast<LoadInst>(&I)) {
              //printf("got load instruction\n");
              Value* pointer = li->getPointerOperand();
              Value* size = ConstantInt::get(IntegerType::get(F.getContext(), 64), dataLayout->getTypeSizeInBits(li->getPointerOperand()->getType()), false);
              Type *PtrTy = PointerType::getUnqual(IntegerType::getInt8Ty(F.getContext()));
              CastInst* castPointer = CastInst::Create(Instruction::BitCast, pointer, PtrTy, "", &I);
              Value* args[] = {castPointer, size};
              CallInst::Create(verifierFunction, ArrayRef<Value*>(args, 2), "", &I);
            } else if (StoreInst* si = dyn_cast<StoreInst>(&I)) {
              //printf("got store instruction");
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
    /*for (auto& F : m) {
      if(!Naming::isSmackName(F.getName())) {
        F.print(errs());
      }
    }*/
    return false;
  }

  // Pass ID variable
  char MemoryAllocationChecker::ID = 0;
  //static RegisterPass<MemoryAllocationChecker> MemoryAllocationCheckerPass("memory-allocation-checker", "SMACK Memory Allocation Checker");
}
