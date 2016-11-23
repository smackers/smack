//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/MemorySafetyChecker.h"
#include "smack/Naming.h"
#include "smack/SmackOptions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Constants.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/ValueSymbolTable.h"
#include "llvm/IR/IntrinsicInst.h"

namespace smack {

using namespace llvm;

void insertMemoryLeakCheck(Function& F, Module& m) {
  Function* memoryLeakCheckFunction = m.getFunction(Naming::MEMORY_LEAK_FUNCTION);
  assert (memoryLeakCheckFunction != NULL && "Memory leak check function must be present");
  for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
    if (isa<ReturnInst>(&*I)) {
      CallInst::Create(memoryLeakCheckFunction, "", &*I);
    }
  }
}

bool MemorySafetyChecker::runOnModule(Module& m) {
  DataLayout* dataLayout = new DataLayout(&m);
  Function* memorySafetyFunction = m.getFunction(Naming::MEMORY_SAFETY_FUNCTION);
  assert(memorySafetyFunction != NULL && "Couldn't find memory safety function");
  for (auto& F : m) {
    if (!Naming::isSmackName(F.getName())) {
      if (SmackOptions::isEntryPoint(F.getName())) {
        insertMemoryLeakCheck(F, m);
      }
      for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
        Value* pointer = NULL;
        if (LoadInst* li = dyn_cast<LoadInst>(&*I)) {
          pointer = li->getPointerOperand();
        } else if (StoreInst* si = dyn_cast<StoreInst>(&*I)) {
          pointer = si->getPointerOperand();
        } else if (MemSetInst* memseti = dyn_cast<MemSetInst>(&*I)) {
	    Value* dest = memseti->getDest();
	    Value* size = memseti->getLength();
	    Type* voidPtrTy = PointerType::getUnqual(IntegerType::getInt8Ty(F.getContext()));
	    CastInst* castPtr = CastInst::Create(Instruction::BitCast, dest, voidPtrTy, "", &*I);
	    CallInst::Create(memorySafetyFunction, {castPtr, size}, "", &*I);
        } else if (MemTransferInst* memtrni = dyn_cast<MemTransferInst>(&*I)) {
            //MemTransferInst is abstract class for both MemCpyInst and MemTransferInst
	    Value* dest = memtrni->getDest();
	    Value* src = memtrni->getSource();
	    Value* size = memtrni->getLength();
	    Type* voidPtrTy = PointerType::getUnqual(IntegerType::getInt8Ty(F.getContext()));
	    CastInst* castPtrDest = CastInst::Create(Instruction::BitCast, dest, voidPtrTy, "", &*I);
	    CastInst* castPtrSrc = CastInst::Create(Instruction::BitCast, src, voidPtrTy, "", &*I);
	    CallInst::Create(memorySafetyFunction, {castPtrDest, size}, "", &*I);  
	    CallInst::Create(memorySafetyFunction, {castPtrSrc, size}, "", &*I);  
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

