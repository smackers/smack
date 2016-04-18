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
        if (LoadInst* li = dyn_cast<LoadInst>(&*I)) {
          Value* pointer = li->getPointerOperand();
          Type* pointerType = pointer->getType();
          uint64_t storeSize = dataLayout->getTypeStoreSize(dyn_cast<PointerType>(pointerType)->getPointerElementType());
          Type* sizeType = memorySafetyFunction->getValueSymbolTable().lookup(Naming::MEMORY_SAFETY_FUNCTION_PARAMETER_SIZE)->getType();
          Value* size = ConstantInt::get(sizeType, storeSize);
          Type *PtrTy = PointerType::getUnqual(IntegerType::getInt8Ty(F.getContext()));
          CastInst* castPointer = CastInst::Create(Instruction::BitCast, pointer, PtrTy, "", &*I);
          Value* args[] = {castPointer, size};
          CallInst::Create(memorySafetyFunction, ArrayRef<Value*>(args, 2), "", &*I);
        } else if (StoreInst* si = dyn_cast<StoreInst>(&*I)) {
          Value* pointer = si->getPointerOperand();
          Type* pointerType = pointer->getType();
          uint64_t storeSize = dataLayout->getTypeStoreSize(dyn_cast<PointerType>(pointerType)->getPointerElementType());
          Type* sizeType = memorySafetyFunction->getValueSymbolTable().lookup(Naming::MEMORY_SAFETY_FUNCTION_PARAMETER_SIZE)->getType();
          Value* size = ConstantInt::get(sizeType, storeSize);
          Type *ptrTy = PointerType::getUnqual(IntegerType::getInt8Ty(F.getContext()));
          CastInst* castPointer = CastInst::Create(Instruction::BitCast, pointer, ptrTy, "", &*I);
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
