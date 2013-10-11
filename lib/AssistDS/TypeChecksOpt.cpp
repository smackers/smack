//===---------- TypeChecksOpt.h - Remove safe runtime type checks ---------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass removes type checks that are statically proven safe
//
//===----------------------------------------------------------------------===//

#include "assistDS/TypeChecksOpt.h"
#include "llvm/IR/Constants.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Module.h"
#include "llvm/Assembly/Writer.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/ADT/Statistic.h"

#include <vector>

using namespace llvm;

char TypeChecksOpt::ID = 0;

static RegisterPass<TypeChecksOpt> 
TC("typechecks-opt", "Remove safe runtime type checks", false, true);

// Pass statistics
STATISTIC(numSafe,  "Number of statically proven safe type checks");

static Type *VoidTy = 0;
static Type *Int8Ty = 0;
static Type *Int32Ty = 0;
static Type *Int64Ty = 0;
static PointerType *VoidPtrTy = 0;
static Type *TypeTagTy = 0;
static Type *TypeTagPtrTy = 0;
static Constant *trackGlobal;
static Constant *trackStringInput;
static Constant *trackInitInst;
static Constant *trackUnInitInst;
static Constant *trackStoreInst;
static Constant *copyTypeInfo;
static Constant *setTypeInfo;
static Constant *checkTypeInst;
static Constant *getTypeTag;
static Constant *MallocFunc;

bool TypeChecksOpt::runOnModule(Module &M) {
  TS = &getAnalysis<dsa::TypeSafety<TDDataStructures> >();

  // Create the necessary prototypes
  VoidTy = IntegerType::getVoidTy(M.getContext());
  Int8Ty = IntegerType::getInt8Ty(M.getContext());
  Int32Ty = IntegerType::getInt32Ty(M.getContext());
  Int64Ty = IntegerType::getInt64Ty(M.getContext());
  VoidPtrTy = PointerType::getUnqual(Int8Ty);
  TypeTagTy = Int8Ty;
  TypeTagPtrTy = PointerType::getUnqual(TypeTagTy);

  Constant *memsetF = M.getOrInsertFunction ("llvm.memset.i64", VoidTy,
                                             VoidPtrTy,
                                             Int8Ty,
                                             Int64Ty,
                                             Int32Ty,
                                             NULL);
  trackGlobal = M.getOrInsertFunction("trackGlobal",
                                      VoidTy,
                                      VoidPtrTy,/*ptr*/
                                      TypeTagTy,/*type*/
                                      Int64Ty,/*size*/
                                      Int32Ty,/*tag*/
                                      NULL);
  trackInitInst = M.getOrInsertFunction("trackInitInst",
                                        VoidTy,
                                        VoidPtrTy,/*ptr*/
                                        Int64Ty,/*size*/
                                        Int32Ty,/*tag*/
                                        NULL);
  trackUnInitInst = M.getOrInsertFunction("trackUnInitInst",
                                          VoidTy,
                                          VoidPtrTy,/*ptr*/
                                          Int64Ty,/*size*/
                                          Int32Ty,/*tag*/
                                          NULL);
  trackStoreInst = M.getOrInsertFunction("trackStoreInst",
                                         VoidTy,
                                         VoidPtrTy,/*ptr*/
                                         TypeTagTy,/*type*/
                                         Int64Ty,/*size*/
                                         Int32Ty,/*tag*/
                                         NULL);
  checkTypeInst = M.getOrInsertFunction("checkType",
                                        VoidTy,
                                        TypeTagTy,/*type*/
                                        Int64Ty,/*size*/
                                        TypeTagPtrTy,
                                        VoidPtrTy,/*ptr*/
                                        Int32Ty,/*tag*/
                                        NULL);
  copyTypeInfo = M.getOrInsertFunction("copyTypeInfo",
                                       VoidTy,
                                       VoidPtrTy,/*dest ptr*/
                                       VoidPtrTy,/*src ptr*/
                                       Int64Ty,/*size*/
                                       Int32Ty,/*tag*/
                                       NULL);
  setTypeInfo = M.getOrInsertFunction("setTypeInfo",
                                      VoidTy,
                                      VoidPtrTy,/*dest ptr*/
                                      TypeTagPtrTy,/*metadata*/
                                      Int64Ty,/*size*/
                                      TypeTagTy,
                                      VoidPtrTy,
                                      Int32Ty,/*tag*/
                                      NULL);
  trackStringInput = M.getOrInsertFunction("trackStringInput",
                                           VoidTy,
                                           VoidPtrTy,
                                           Int32Ty,
                                           NULL);
  getTypeTag = M.getOrInsertFunction("getTypeTag",
                                     VoidTy,
                                     VoidPtrTy, /*ptr*/
                                     Int64Ty, /*size*/
                                     TypeTagPtrTy, /*dest for type tag*/
                                     Int32Ty, /*tag*/
                                     NULL);
  MallocFunc = M.getFunction("malloc");

  for(Value::use_iterator User = trackGlobal->use_begin(); User != trackGlobal->use_end(); ++User) {
    CallInst *CI = dyn_cast<CallInst>(*User);
    assert(CI);
    if(TS->isTypeSafe(CI->getOperand(1)->stripPointerCasts(), CI->getParent()->getParent())) {
      std::vector<Value*>Args;
      Args.push_back(CI->getOperand(1));
      Args.push_back(CI->getOperand(3));
      Args.push_back(CI->getOperand(4));
      CallInst::Create(trackInitInst, Args, "", CI);
      toDelete.push_back(CI);
    }
  }

  for(Value::use_iterator User = checkTypeInst->use_begin(); User != checkTypeInst->use_end(); ++User) {
    CallInst *CI = dyn_cast<CallInst>(*User);
    assert(CI);

    if(TS->isTypeSafe(CI->getOperand(4)->stripPointerCasts(), CI->getParent()->getParent())) {
      toDelete.push_back(CI);
    }
  }

  for(Value::use_iterator User = trackStoreInst->use_begin(); User != trackStoreInst->use_end(); ++User) {
    CallInst *CI = dyn_cast<CallInst>(*User);
    assert(CI);

    if(TS->isTypeSafe(CI->getOperand(1)->stripPointerCasts(), CI->getParent()->getParent())) {
      toDelete.push_back(CI);
    }
  }

  // for alloca's if they are type known
  // assume initialized with TOP
  for(Value::use_iterator User = trackUnInitInst->use_begin(); User != trackUnInitInst->use_end(); ) {
    CallInst *CI = dyn_cast<CallInst>(*(User++));
    assert(CI);

    // check if operand is an alloca inst.
    if(TS->isTypeSafe(CI->getOperand(1)->stripPointerCasts(), CI->getParent()->getParent())) {
      CI->setCalledFunction(trackInitInst);

      if(AllocaInst *AI = dyn_cast<AllocaInst>(CI->getOperand(1)->stripPointerCasts())) {
        // Initialize the allocation to NULL
        std::vector<Value *> Args2;
        Args2.push_back(CI->getOperand(1));
        Args2.push_back(ConstantInt::get(Int8Ty, 0));
        Args2.push_back(CI->getOperand(2));
        Args2.push_back(ConstantInt::get(Int32Ty, AI->getAlignment()));
        CallInst::Create(memsetF, Args2, "", CI);
      }
    }
  }

  if(MallocFunc) {
    for(Value::use_iterator User = MallocFunc->use_begin(); User != MallocFunc->use_end(); User ++) {
      CallInst *CI = dyn_cast<CallInst>(*User);
      if(!CI)
        continue;
      if(TS->isTypeSafe(CI, CI->getParent()->getParent())){
        CastInst *BCI = BitCastInst::CreatePointerCast(CI, VoidPtrTy);
        CastInst *Size = CastInst::CreateSExtOrBitCast(CI->getOperand(1), Int64Ty);
        Size->insertAfter(CI);
        BCI->insertAfter(Size);
        std::vector<Value *>Args;
        Args.push_back(BCI);
        Args.push_back(Size);
        Args.push_back(ConstantInt::get(Int32Ty, 0));
        CallInst *CINew = CallInst::Create(trackInitInst, Args);
        CINew->insertAfter(BCI);
      }
    }
  }

  // also do for mallocs/calloc/other allocators???
  // other allocators??

  for(Value::use_iterator User = copyTypeInfo->use_begin(); User != copyTypeInfo->use_end(); ++User) {
    CallInst *CI = dyn_cast<CallInst>(*User);
    assert(CI);

    if(TS->isTypeSafe(CI->getOperand(1)->stripPointerCasts(), CI->getParent()->getParent())) {
      std::vector<Value*> Args;
      Args.push_back(CI->getOperand(1));
      Args.push_back(CI->getOperand(3)); // size
      Args.push_back(CI->getOperand(4));
      CallInst::Create(trackInitInst, Args, "", CI);
      toDelete.push_back(CI);
    }
  }
  for(Value::use_iterator User = setTypeInfo->use_begin(); User != setTypeInfo->use_end(); ++User) {
    CallInst *CI = dyn_cast<CallInst>(*User);
    assert(CI);

    if(TS->isTypeSafe(CI->getOperand(1)->stripPointerCasts(), CI->getParent()->getParent())) {
      std::vector<Value*> Args;
      Args.push_back(CI->getOperand(1));
      Args.push_back(CI->getOperand(3)); // size
      Args.push_back(CI->getOperand(6));
      CallInst::Create(trackInitInst, Args, "", CI);
      toDelete.push_back(CI);
    }
  }

  for(Value::use_iterator User = getTypeTag->use_begin(); User != getTypeTag->use_end(); ++User) {
    CallInst *CI = dyn_cast<CallInst>(*User);
    assert(CI);
    if(TS->isTypeSafe(CI->getOperand(1)->stripPointerCasts(), CI->getParent()->getParent())) {
      AllocaInst *AI = dyn_cast<AllocaInst>(CI->getOperand(3)->stripPointerCasts());
      assert(AI);
      std::vector<Value*>Args;
      Args.push_back(CI->getOperand(3));
      Args.push_back(ConstantInt::get(Int8Ty, 255));
      Args.push_back(CI->getOperand(2));
      Args.push_back(ConstantInt::get(Int32Ty, AI->getAlignment()));
      CallInst::Create(memsetF, Args, "", CI);
      toDelete.push_back(CI);
    }
  }

  numSafe += toDelete.size();

  while(!toDelete.empty()) {
    Instruction *I = toDelete.back();
    toDelete.pop_back();
    I->eraseFromParent();
  }

  return (numSafe > 0);
}


