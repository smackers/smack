//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACKINSTVISITOR_H
#define SMACKINSTVISITOR_H

#include "BoogieAst.h"

#include "llvm/ADT/SmallVector.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/GetElementPtrTypeIterator.h"
#include "llvm/Support/InstVisitor.h"
#include "llvm/DataLayout.h"

using namespace llvm;

namespace smack {

class SmackInstVisitor : public InstVisitor<SmackInstVisitor> {
private:
  DataLayout *targetData;
  Procedure *currProc;
  Block *currBlock;
  
  void generateCall(string p, vector<Expr*> ps, vector<string> rs);

public:
  SmackInstVisitor(DataLayout *td, Procedure *p, Block *b) 
      : targetData(td), currProc(p), currBlock(b) {}  
  void setCurrBlock(Block *b) { currBlock = b; }
  Expr * expr(Value *v);
  Expr * operand(Value *v);
      
  void visitInstruction(Instruction& i);
  void processInstruction(Instruction& i);
  void visitAllocaInst(AllocaInst& i);
  void visitBranchInst(BranchInst& i);
  void visitPHINode(PHINode& i);
  void visitTruncInst(TruncInst& i);
  void visitUnreachableInst(UnreachableInst& i);
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
  
  
  // void visitAtomicCmpXchgInst(AtomicCmpXchgInst &I);
  // void visitPtrToIntInst(PtrToIntInst &I);
};
}

#endif  /*SMACKINSTVISITOR_H*/
