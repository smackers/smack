//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACKINSTVISITOR_H
#define SMACKINSTVISITOR_H

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/InstVisitor.h"
#include <set>
#include <unordered_set>

namespace smack {

class Naming;
class Program;
class ProcDecl;
class Block;
class Stmt;
class Expr;
class Attr;
class SmackRep;

class SmackInstGenerator : public llvm::InstVisitor<SmackInstGenerator> {

private:
  llvm::LoopInfo &loops;
  SmackRep *rep;
  ProcDecl *proc;
  Naming *naming;

  Block *currBlock;
  llvm::BasicBlock::const_iterator nextInst;
  std::map<const llvm::BasicBlock *, Block *> blockMap;
  std::map<const llvm::Value *, std::string> sourceNames;

  Block *createBlock();
  Block *getBlock(llvm::BasicBlock *bb);

  void generatePhiAssigns(llvm::Instruction &i);
  void generateGotoStmts(
      llvm::Instruction &i,
      std::vector<std::pair<const Expr *, llvm::BasicBlock *>> target);
  void processInstruction(llvm::Instruction &i);
  void nameInstruction(llvm::Instruction &i);
  void annotate(llvm::Instruction &i, Block *b);

  const Stmt *recordProcedureCall(const llvm::Value *V,
                                  std::list<const Attr *> attrs);

public:
  void emit(const Stmt *s);

public:
  SmackInstGenerator(llvm::LoopInfo &LI, SmackRep *R, ProcDecl *P, Naming *N)
      : loops(LI), rep(R), proc(P), naming(N) {}

  void visitBasicBlock(llvm::BasicBlock &bb);
  void visitInstruction(llvm::Instruction &i);

  void visitReturnInst(llvm::ReturnInst &i);
  void visitBranchInst(llvm::BranchInst &i);
  void visitSwitchInst(llvm::SwitchInst &i);
  // TODO implement indirectbr
  void visitInvokeInst(llvm::InvokeInst &i);
  void visitResumeInst(llvm::ResumeInst &i);
  void visitUnreachableInst(llvm::UnreachableInst &i);

  void visitBinaryOperator(llvm::BinaryOperator &I);
  void visitUnaryOperator(llvm::UnaryOperator &I);

  void visitExtractElementInst(llvm::ExtractElementInst &I);
  void visitInsertElementInst(llvm::InsertElementInst &I);
  void visitShuffleVectorInst(llvm::ShuffleVectorInst &I);

  void visitExtractValueInst(llvm::ExtractValueInst &i);
  void visitInsertValueInst(llvm::InsertValueInst &i);

  void visitAllocaInst(llvm::AllocaInst &i);
  void visitLoadInst(llvm::LoadInst &i);
  void visitStoreInst(llvm::StoreInst &i);
  // TODO implement fence
  void visitAtomicCmpXchgInst(llvm::AtomicCmpXchgInst &i);
  void visitAtomicRMWInst(llvm::AtomicRMWInst &i);
  void visitGetElementPtrInst(llvm::GetElementPtrInst &i);

  void visitCastInst(llvm::CastInst &I);
  void visitCmpInst(llvm::CmpInst &I);

  void visitPHINode(llvm::PHINode &i);
  void visitSelectInst(llvm::SelectInst &i);
  void visitCallInst(llvm::CallInst &i);
  void visitCallBrInst(llvm::CallBrInst &i);
  void visitDbgValueInst(llvm::DbgValueInst &i);
  // TODO implement va_arg
  void visitLandingPadInst(llvm::LandingPadInst &i);

  void visitMemCpyInst(llvm::MemCpyInst &i);
  void visitMemSetInst(llvm::MemSetInst &i);
  void visitIntrinsicInst(llvm::IntrinsicInst &i);
};
} // namespace smack

#endif // SMACKINSTVISITOR_H
