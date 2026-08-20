//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACKINSTVISITOR_H
#define SMACKINSTVISITOR_H

#include "smack/FunctionalLoopSummary.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/InstVisitor.h"
#include <map>
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
  llvm::ScalarEvolution *scalarEvolution;
  llvm::AAResults *aliasAnalysis;
  llvm::MemorySSA *memorySSA;
  bool emitLoopBoundWarnings;
  SmackRep *rep;
  ProcDecl *proc;
  Naming *naming;

  Block *currBlock;
  llvm::BasicBlock::const_iterator nextInst;
  std::map<const llvm::BasicBlock *, Block *> blockMap;
  std::map<const llvm::Value *, std::string> sourceNames;
  std::vector<FunctionalLoopSummary> functionalLoops;
  std::map<const llvm::BranchInst *, const FunctionalLoopSummary *>
      summariesByPreheader;
  std::set<const llvm::BasicBlock *> suppressedBlocks;
  unsigned functionalLoopId = 0;

  Block *createBlock();
  Block *getBlock(llvm::BasicBlock *bb);

  void generatePhiAssigns(llvm::Instruction &i);
  void generateGotoStmts(
      llvm::Instruction &i,
      std::vector<std::pair<const Expr *, llvm::BasicBlock *>> target);
  void processInstruction(llvm::Instruction &i);
  void nameInstruction(llvm::Instruction &i);
  void annotate(llvm::Instruction &i, Block *b);
  void prepareFunctionalLoops(llvm::Function &F);
  void emitFunctionalLoop(const FunctionalLoopSummary &summary);
  const Expr *functionalIntegerSCEV(const llvm::SCEV *scev);
  const Expr *functionalPointerSCEV(const llvm::SCEV *scev);
  const Expr *functionalInductionValue(
      const FunctionalLoopSummary &summary, const Expr *iteration);
  const Expr *functionalAddress(const AffineLoopAccess &access,
                                const Expr *iteration,
                                const llvm::IntegerType *iterationType);
  const Expr *
  functionalValue(const llvm::Value *value,
                  const FunctionalLoopSummary &summary, const Expr *iteration,
                  const std::map<std::string, std::string> &entryMemories);

  const Stmt *recordProcedureCall(const llvm::Value *V,
                                  std::list<const Attr *> attrs);

public:
  void emit(const Stmt *s);
  void generateFunction(llvm::Function &F);

public:
  SmackInstGenerator(llvm::LoopInfo &LI, llvm::ScalarEvolution *SE,
                     llvm::AAResults *AA, llvm::MemorySSA *MSSA, SmackRep *R,
                     ProcDecl *P, Naming *N, bool EmitLoopBoundWarnings = false)
      : loops(LI), scalarEvolution(SE), aliasAnalysis(AA), memorySSA(MSSA),
        emitLoopBoundWarnings(EmitLoopBoundWarnings), rep(R), proc(P),
        naming(N) {}

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
