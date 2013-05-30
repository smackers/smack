//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACKINSTVISITOR_H
#define SMACKINSTVISITOR_H

#include "BoogieAst.h"
#include "Values.h"
#include "llvm/Support/InstVisitor.h"

using namespace llvm;

namespace smack {

class SmackInstVisitor : public InstVisitor<SmackInstVisitor> {
private:
  Values& values;
  Procedure *currProc;
  Block *currBlock;
  
  Stmt * generateCall(Function *f, vector<Expr*> ps, vector<string> rs);

public:
  SmackInstVisitor(Values& v, Procedure *p, Block *b) 
      : values(v), currProc(p), currBlock(b) {}  
  void setCurrBlock(Block *b) { currBlock = b; }
  Block * getCurrBlock() { return currBlock; }

  void processInstruction(Instruction& i);
  void visitInstruction(Instruction& i);
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
  void visitPtrToIntInst(PtrToIntInst& i);
  void visitIntToPtrInst(IntToPtrInst& i);
  
  // void visitAtomicCmpXchgInst(AtomicCmpXchgInst &I);
};
}

#endif  /*SMACKINSTVISITOR_H*/
