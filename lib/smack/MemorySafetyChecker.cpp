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

namespace smack {

using namespace llvm;

void insertMemoryLeakStatement(Function& F, Module& m) {
  Function* memoryLeakCheckFunction = m.getFunction(Naming::MEMORY_LEAK_CHECK_FUNCTION);
  for(inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
    if(isa<ReturnInst>(&*I)) {
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
        insertMemoryLeakStatement(F, m);
      }
      for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
        Value* pointer = NULL;
        if (LoadInst* li = dyn_cast<LoadInst>(&*I)) {
          pointer = li->getPointerOperand();
        } else if (StoreInst* si = dyn_cast<StoreInst>(&*I)) {
          pointer = si->getPointerOperand();
        } else if (CallInst* ci = dyn_cast<CallInst>(&*I)) {
          Function* calledF = ci->getCalledFunction();
          if(calledF && calledF->getName().find(Naming::INTRINSIC_MEMSET) != std::string::npos) {
	    Value* dest = ci->getArgOperand(0);
	    Value* size = ci->getArgOperand(2);
	    Type* voidPtrTy = PointerType::getUnqual(IntegerType::getInt8Ty(F.getContext()));
	    CastInst* castPtr = CastInst::Create(Instruction::BitCast, dest, voidPtrTy, "", &*I);
	    Value* args[] = {castPtr, size};
	    CallInst::Create(memorySafetyFunction, ArrayRef<Value*>(args, 2), "", &*I);
	  } else if(calledF && calledF->getName().find(Naming::INTRINSIC_MEMSET) != std::string::npos) {
	    Value* dest = ci->getArgOperand(0);
	    Value* src = ci->getArgOperand(1);
	    Value* size = ci->getArgOperand(2);
	    Type* voidPtrTy = PointerType::getUnqual(IntegerType::getInt8Ty(F.getContext()));
	    CastInst* castPtrDest = CastInst::Create(Instruction::BitCast, dest, voidPtrTy, "", &*I);
	    CastInst* castPtrSrc = CastInst::Create(Instruction::BitCast, src, voidPtrTy, "", &*I);
	    Value* argsDest[] = {castPtrDest, size};
	    Value* argsSrc[] = {castPtrSrc, size};
	    CallInst::Create(memorySafetyFunction, ArrayRef<Value*>(argsDest, 2), "", &*I);  
	    CallInst::Create(memorySafetyFunction, ArrayRef<Value*>(argsSrc, 2), "", &*I);  
	  }
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

