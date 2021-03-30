//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/MemorySafetyChecker.h"
#include "smack/Debug.h"
#include "smack/Naming.h"
#include "smack/SmackOptions.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/ValueSymbolTable.h"

namespace smack {

using namespace llvm;

Function *MemorySafetyChecker::getLeakCheckFunction(Module &M) {
  auto F = M.getFunction(Naming::MEMORY_LEAK_FUNCTION);
  assert(F && "Memory leak check function must be present.");
  return F;
}

Function *MemorySafetyChecker::getSafetyCheckFunction(Module &M) {
  auto F = M.getFunction(Naming::MEMORY_SAFETY_FUNCTION);
  assert(F && "Memory safety check function must be present.");
  F->setDoesNotAccessMemory();
  F->setDoesNotThrow();
  return F;
}

void MemorySafetyChecker::copyDbgMetadata(Instruction *src, Instruction *dst) {
  dst->setMetadata("dbg", src->getMetadata("dbg"));
}

void MemorySafetyChecker::insertMemoryLeakCheck(Instruction *I) {
  auto &M = *I->getParent()->getParent()->getParent();
  auto ci = CallInst::Create(getLeakCheckFunction(M), "", I);
  copyDbgMetadata(I, ci);
}

void MemorySafetyChecker::insertMemoryAccessCheck(Value *addr, Value *size,
                                                  Instruction *I) {
  auto &M = *I->getParent()->getParent()->getParent();
  auto &C = M.getContext();
  auto T = PointerType::getUnqual(Type::getInt8Ty(C));
  auto ptrArg = CastInst::Create(Instruction::BitCast, addr, T, "", I);
  auto sizeArg = CastInst::CreateBitOrPointerCast(size, T, "", I);
  auto ci =
      CallInst::Create(getSafetyCheckFunction(M), {ptrArg, sizeArg}, "", I);
  copyDbgMetadata(I, ptrArg);
  copyDbgMetadata(I, sizeArg);
  copyDbgMetadata(I, ci);
}

bool MemorySafetyChecker::runOnFunction(Function &F) {
  if (Naming::isSmackName(F.getName()) ||
      !SmackOptions::shouldCheckFunction(F.getName()))
    return false;

  this->visit(F);
  return true;
}

void MemorySafetyChecker::visitReturnInst(llvm::ReturnInst &I) {
  auto &F = *I.getParent()->getParent();

  if (SmackOptions::isEntryPoint(F.getName()))
    insertMemoryLeakCheck(&I);
}

namespace {
Value *accessSizeAsPointer(Module &M, Value *V) {
  auto T = dyn_cast<PointerType>(V->getType());
  assert(T && "expected pointer type");

  return ConstantExpr::getIntToPtr(
      ConstantInt::get(
          Type::getInt64Ty(M.getContext()),
          M.getDataLayout().getTypeStoreSize(T->getPointerElementType())),
      PointerType::getUnqual(Type::getInt8Ty(M.getContext())));
}

Value *accessSizeAsPointer(LoadInst &I) {
  auto &M = *I.getParent()->getParent()->getParent();
  return accessSizeAsPointer(M, I.getPointerOperand());
}

Value *accessSizeAsPointer(StoreInst &I) {
  auto &M = *I.getParent()->getParent()->getParent();
  return accessSizeAsPointer(M, I.getPointerOperand());
}
} // namespace

void MemorySafetyChecker::visitLoadInst(LoadInst &I) {
  insertMemoryAccessCheck(I.getPointerOperand(), accessSizeAsPointer(I), &I);
}

void MemorySafetyChecker::visitStoreInst(StoreInst &I) {
  insertMemoryAccessCheck(I.getPointerOperand(), accessSizeAsPointer(I), &I);
}

void MemorySafetyChecker::visitMemSetInst(MemSetInst &I) {
  insertMemoryAccessCheck(I.getDest(), I.getLength(), &I);
}

void MemorySafetyChecker::visitMemTransferInst(MemTransferInst &I) {
  insertMemoryAccessCheck(I.getDest(), I.getLength(), &I);
  insertMemoryAccessCheck(I.getSource(), I.getLength(), &I);
}

// Pass ID variable
char MemorySafetyChecker::ID = 0;
} // namespace smack
