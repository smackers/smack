//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACKINSTVISITOR_H
#define SMACKINSTVISITOR_H

#include "smack/BoogieAst.h"
#include "smack/SmackRep.h"
#include "llvm/InstVisitor.h"
#include <unordered_set>

namespace smack {
  
class SmackInstGenerator : public llvm::InstVisitor<SmackInstGenerator> {

private:
  SmackRep& rep;
  CodeContainer& proc;
  Block* currBlock;
  map<const llvm::BasicBlock*, Block*> blockMap;
  int blockNum;
  int varNum;
  int varNs;
  vector<const Expr*>* extracted;

  string createVar();
  Block* createBlock();
  Block* getBlock(llvm::BasicBlock* bb);

  void generatePhiAssigns(llvm::TerminatorInst& i);
  void generateGotoStmts(llvm::Instruction& i,
                         vector<pair<const Expr*, llvm::BasicBlock*> > target);
  void processInstruction(llvm::Instruction& i);
  void nameInstruction(llvm::Instruction& i);
  void annotate(llvm::Instruction& i, Block* b);

  void addDecl(Decl* d) { proc.addDecl(d); }
  void addMod(string x) { proc.addMod(x); }
  void addTopDecl(Decl* d) { proc.getProg().addDecl(d); }
  void addBlock(Block* b) { proc.addBlock(b); }

  void emit(const Stmt* s) { currBlock->addStmt(s); }

public:
  SmackInstGenerator(SmackRep& r, CodeContainer& p, int varNamespace = -1)
    : rep(r), proc(p), blockNum(0), varNum(0), varNs(varNamespace) {}
  
  void setExtracted(vector<const Expr*>& e) { extracted = &e; }
  const Expr* getExtracted(llvm::Value* V) {
    using namespace llvm;
    if (ConstantInt* CI = dyn_cast<ConstantInt>(V)) {
      uint64_t i = CI->getLimitedValue();
      assert(extracted && extracted->size() > i && "Did not find extracted expression.");
      return (*extracted)[i];
    }
    assert(false && "Unexpected value.");
  }
  
  void visitSlice(llvm::Function* F, unordered_set<llvm::Instruction*> slice) {
    using namespace llvm;
    for (Function::iterator B = F->begin(), E = F->end(); B != E; ++B) {
      bool blockVisited = false;
      for (BasicBlock::iterator I = B->begin(), G = B->end(); I != G; ++I) {
        if (slice.count(&*I)) {
          if (!blockVisited) {
            visitBasicBlock(*B);
            blockVisited = true;
          }
          visit(*I);
        }
      }
      // TODO WHAT TO DO WITH TERMINATORLESS BLOCKS?
    }
  }

  void visitBasicBlock(llvm::BasicBlock& bb);
  void visitInstruction(llvm::Instruction& i);

  void visitReturnInst(llvm::ReturnInst& i);
  void visitBranchInst(llvm::BranchInst& i);
  void visitSwitchInst(llvm::SwitchInst& i);
  // TODO implement indirectbr
  // TODO implement invoke
  // TODO implement resume
  void visitUnreachableInst(llvm::UnreachableInst& i);
  
  void visitBinaryOperator(llvm::BinaryOperator& i);

  // TODO implement extractelement
  // TODO implement insertelement
  // TODO implement shufflevector

  // TODO implement extractvalue
  // TODO implement insertvalue
  
  void visitAllocaInst(llvm::AllocaInst& i);
  void visitLoadInst(llvm::LoadInst& i);
  void visitStoreInst(llvm::StoreInst& i);
  // TODO implement fence
  void visitAtomicCmpXchgInst(llvm::AtomicCmpXchgInst& i);
  void visitAtomicRMWInst(llvm::AtomicRMWInst& i);
  void visitGetElementPtrInst(llvm::GetElementPtrInst& i);

  void visitTruncInst(llvm::TruncInst& i);
  void visitZExtInst(llvm::ZExtInst& i);
  void visitSExtInst(llvm::SExtInst& i);
  void visitFPTruncInst(llvm::FPTruncInst& i);
  void visitFPExtInst(llvm::FPExtInst& i);
  void visitFPToUIInst(llvm::FPToUIInst& i);
  void visitFPToSIInst(llvm::FPToSIInst& i);
  void visitUIToFPInst(llvm::UIToFPInst& i);
  void visitSIToFPInst(llvm::SIToFPInst& i);
  void visitPtrToIntInst(llvm::PtrToIntInst& i);
  void visitIntToPtrInst(llvm::IntToPtrInst& i);
  void visitBitCastInst(llvm::BitCastInst& i);
  // TODO implement addrspacecast

  void visitICmpInst(llvm::ICmpInst& i);
  void visitFCmpInst(llvm::FCmpInst& i);
  void visitPHINode(llvm::PHINode& i);
  void visitSelectInst(llvm::SelectInst& i);
  void visitCallInst(llvm::CallInst& i);
  // TODO implement va_arg
  // TODO landingpad
  
  void visitMemCpyInst(llvm::MemCpyInst& i);
  void visitMemSetInst(llvm::MemSetInst& i);
};
}

#endif // SMACKINSTVISITOR_H
