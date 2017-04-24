//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACKINSTVISITOR_H
#define SMACKINSTVISITOR_H

#include "smack/BoogieAst.h"
#include "smack/SmackRep.h"
#include "smack/Naming.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/Analysis/LoopInfo.h"
#include <unordered_set>
#include <set>

namespace smack {

class SmackInstGenerator : public llvm::InstVisitor<SmackInstGenerator> {

private:
  LoopInfo& loops;
  SmackRep& rep;
  ProcDecl& proc;
  Naming& naming;

  Block* currBlock;
  llvm::BasicBlock::const_iterator nextInst;
  std::map<const llvm::BasicBlock*, Block*> blockMap;
  std::map<const llvm::Value*, std::string> sourceNames;

  Block* createBlock();
  Block* getBlock(llvm::BasicBlock* bb);

  void generatePhiAssigns(llvm::TerminatorInst& i);
  void generateGotoStmts(llvm::Instruction& i,
                         std::vector<std::pair<const Expr*, llvm::BasicBlock*> > target);
  void processInstruction(llvm::Instruction& i);
  void nameInstruction(llvm::Instruction& i);
  void annotate(llvm::Instruction& i, Block* b);

  const Stmt* recordProcedureCall(llvm::Value* V, std::list<const Attr*> attrs);

public:
  void emit(const Stmt* s) {
    // stringstream str;
    // s->print(str);
    // DEBUG(llvm::errs() << "emit:   " << str.str() << "\n");
    currBlock->addStmt(s);
  }

public:
  SmackInstGenerator(LoopInfo& LI, SmackRep& R, ProcDecl& P, Naming& N)
    : loops(LI), rep(R), proc(P), naming(N) {}


  void visitBasicBlock(llvm::BasicBlock& bb);
  void visitInstruction(llvm::Instruction& i);

  void visitReturnInst(llvm::ReturnInst& i);
  void visitBranchInst(llvm::BranchInst& i);
  void visitSwitchInst(llvm::SwitchInst& i);
  // TODO implement indirectbr
  void visitInvokeInst(llvm::InvokeInst& i);
  void visitResumeInst(llvm::ResumeInst& i);
  void visitUnreachableInst(llvm::UnreachableInst& i);

  void visitBinaryOperator(llvm::BinaryOperator& I);

  // TODO implement extractelement
  // TODO implement insertelement
  // TODO implement shufflestd::vector

  void visitExtractValueInst(llvm::ExtractValueInst& i);
  void visitInsertValueInst(llvm::InsertValueInst& i);

  void visitAllocaInst(llvm::AllocaInst& i);
  void visitLoadInst(llvm::LoadInst& i);
  void visitStoreInst(llvm::StoreInst& i);
  // TODO implement fence
  void visitAtomicCmpXchgInst(llvm::AtomicCmpXchgInst& i);
  void visitAtomicRMWInst(llvm::AtomicRMWInst& i);
  void visitGetElementPtrInst(llvm::GetElementPtrInst& i);

  void visitCastInst(llvm::CastInst& I);
  void visitCmpInst(llvm::CmpInst& I);

  void visitPHINode(llvm::PHINode& i);
  void visitSelectInst(llvm::SelectInst& i);
  void visitCallInst(llvm::CallInst& i);
  void visitDbgValueInst(llvm::DbgValueInst& i);
  // TODO implement va_arg
  void visitLandingPadInst(llvm::LandingPadInst& i);

  void visitMemCpyInst(llvm::MemCpyInst& i);
  void visitMemSetInst(llvm::MemSetInst& i);
};
}

#endif // SMACKINSTVISITOR_H
