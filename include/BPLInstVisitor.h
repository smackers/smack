//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef BPLINSTVISITOR_H
#define BPLINSTVISITOR_H

#include "Procedure.h"
#include "BPLModule.h"
#include "Common.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/GetElementPtrTypeIterator.h"
#include "llvm/Support/InstVisitor.h"
#include "llvm/Target/TargetData.h"

using namespace llvm;

namespace smack {

class BPLInstVisitor : public InstVisitor<BPLInstVisitor> {
private:
  TargetData* targetData;
  BPLBlock* block;
  Expr* visitValue(Value* value);
 
public:
  BPLInstVisitor(TargetData* td) : targetData(td) {}
  void setBPLBlock(BPLBlock* blockP);
  void addSuccBlock(BPLBlock* succBlock);
  void visitInstruction(Instruction& i);
  void processInstruction(Instruction& i);
  void visitAllocaInst(AllocaInst& i);
  void visitBranchInst(BranchInst& i);
  void visitPHINode(PHINode& i);
  void visitCallInst(CallInst& i);
  void visitReturnInst(ReturnInst& i);
  void visitLoadInst(LoadInst& i);
  void visitStoreInst(StoreInst& i);
  void visitGetElementPtrInst(GetElementPtrInst& i);
  void visitICmpInst(ICmpInst& i);
  void visitZExtInst(ZExtInst& i);
  void visitSExtInst(SExtInst& i);
  void visitBitCastInst(BitCastInst& i);
  void visitBinaryOperator(BinaryOperator& i);
};
}

#endif  /*BPLINSTVISITOR_H*/
