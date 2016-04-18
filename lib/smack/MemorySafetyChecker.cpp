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
#include "llvm/IR/ValueSymbolTable.h"

namespace smack {

using namespace llvm;

bool MemorySafetyChecker::runOnModule(Module& m) {
  DataLayout* dataLayout = new DataLayout(&m);
  Function* memorySafetyFunction = m.getFunction(Naming::MEMORY_SAFETY_FUNCTION);
  assert(memorySafetyFunction != NULL && "Couldn't find memory safety function");
  for (auto& F : m) {
    if (!Naming::isSmackName(F.getName())) {
      for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
        Value* pointer = NULL;
        if (LoadInst* li = dyn_cast<LoadInst>(&*I)) {
          pointer = li->getPointerOperand();
        } else if (StoreInst* si = dyn_cast<StoreInst>(&*I)) {
          pointer = si->getPointerOperand();
        }

        if (pointer) {
          // Finding the exact type of the second argument to our memory safety function
          Type* sizeType = memorySafetyFunction->getFunctionType()->getParamType(1);
          PointerType* pointerType = cast<PointerType>(pointer->getType());
          uint64_t storeSize = dataLayout->getTypeStoreSize(pointerType->getPointerElementType());
          Value* size = ConstantInt::get(sizeType, storeSize);
          Type *voidPtrTy = PointerType::getUnqual(IntegerType::getInt8Ty(F.getContext()));
          CastInst* castPointer = CastInst::Create(Instruction::BitCast, pointer, voidPtrTy, "", &*I);
          Value* args[] = {castPointer, size};
          CallInst::Create(memorySafetyFunction, ArrayRef<Value*>(args, 2), "", &*I);
        }
      }
    }
  }
  return true;
}

// Pass ID variable
char MemorySafetyChecker::ID = 0;
}

