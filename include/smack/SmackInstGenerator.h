//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACKINSTVISITOR_H
#define SMACKINSTVISITOR_H

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/InstVisitor.h"
#include <map>
#include <set>
#include <string>
#include <unordered_set>
#include <vector>

namespace llvm {
class DbgVariableRecord;
class DbgVariableIntrinsic;
} // namespace llvm

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
  const llvm::Instruction *currentInstruction = nullptr;
  unsigned currentStatementOrdinal = 0;
  llvm::BasicBlock::const_iterator nextInst;
  std::map<const llvm::BasicBlock *, Block *> blockMap;
  std::map<const llvm::Loop *, std::list<const Expr *>> loopInvariants;
  std::map<const llvm::Value *, std::string> sourceNames;

  struct ProvenanceInfo {
    std::string sourceExpr;
    std::set<std::string> sourceVars;
    std::string sourceLhs;
    std::string originCondition;
    std::string loweringKind;
    std::string boogieExpr;
    std::string conditionId;
    std::string sourceOp;
    std::vector<std::string> sourceArgs;
    std::vector<std::string> boogieArgs;
    std::set<std::string> boogieDefs;
    std::set<std::string> boogieUses;
    std::set<std::string> sourceDefs;
    std::set<std::string> sourceUses;
  };
  std::map<const llvm::Value *, ProvenanceInfo> provenance;

  // Cache of source file lines by filename.
  std::map<std::string, std::vector<std::string>> sourceLineCache;
  std::string getSourceLine(const std::string &filename, unsigned line);

  Block *createBlock();
  Block *getBlock(llvm::BasicBlock *bb);

  void generatePhiAssigns(llvm::Instruction &i);
  void generateGotoStmts(
      llvm::Instruction &i,
      std::vector<std::pair<const Expr *, llvm::BasicBlock *>> target);
  void processInstruction(llvm::Instruction &i);
  void recordDebugVariable(const llvm::DbgVariableRecord &i);
  void recordDebugVariable(const llvm::DbgVariableIntrinsic &i);
  void nameInstruction(llvm::Instruction &i);
  void annotate(llvm::Instruction &i, Block *b);
  void hoistLoopStmtToHeader(const llvm::Loop *loop, const Stmt *stmt);
  void hoistLoopStmtsToHeader(const llvm::Loop *loop,
                              std::list<const Stmt *> stmts);
  const llvm::Loop *invariantLoopForHeader(
      const llvm::BasicBlock *header) const;
  void addLoopInvariantChecks(Block *block, const llvm::Loop *loop);
  unsigned instructionIndex(const llvm::Instruction &i) const;
  std::string llvmInstructionId(const llvm::Instruction &i) const;
  std::string exprString(const Expr *expr) const;
  std::string stmtString(const Stmt *stmt) const;
  std::string directSourceName(const llvm::Value *value) const;
  std::string valueName(const llvm::Value *value) const;
  std::string boogieValueExpr(const llvm::Value *value) const;
  std::string sourceExpr(const llvm::Value *value) const;
  std::set<std::string> sourceVars(const llvm::Value *value) const;
  std::string conditionId(const llvm::Value *value) const;
  void addValueUse(ProvenanceInfo &info, const llvm::Value *value) const;
  ProvenanceInfo buildValueProvenance(const llvm::Instruction &inst,
                                      const Expr *boogieExpr,
                                      std::string loweringKind) const;
  void addIndexedAttrs(std::list<const Attr *> &attrs,
                       const std::string &name,
                       const std::vector<std::string> &values) const;
  void addSetAttrs(std::list<const Attr *> &attrs,
                   const std::string &pluralName,
                   const std::string &singularName,
                   const std::set<std::string> &values) const;
  void appendProvenanceInfoAttrs(std::list<const Attr *> &attrs,
                                 const ProvenanceInfo &info) const;
  std::list<const Attr *>
  provenanceAttrs(const Stmt *stmt, std::list<const Attr *> extraAttrs);
  std::list<const Attr *> loopAttrs(const llvm::Loop *loop,
                                    std::string role) const;
  std::list<const Attr *> snapshotAttrs(const llvm::Loop *loop,
                                        const llvm::PHINode *phi) const;
  std::list<const Attr *>
  branchTargetAttrs(const llvm::Instruction &inst,
                    const llvm::BasicBlock *target) const;
  std::list<const Attr *> conditionAttrs(const llvm::Value *condition,
                                         std::string loweringKind) const;
  void addStmt(Block *block, const Stmt *stmt,
               std::list<const Attr *> extraAttrs = {});
  void insertStmt(Block *block, const Stmt *stmt,
                  std::list<const Attr *> extraAttrs = {});
  void emit(const Stmt *s, std::list<const Attr *> extraAttrs);

  const Stmt *recordProcedureCall(const llvm::Value *V,
                                  std::list<const Attr *> attrs);

public:
  void emit(const Stmt *s);

public:
  SmackInstGenerator(llvm::LoopInfo &LI, SmackRep *R, ProcDecl *P, Naming *N)
      : loops(LI), rep(R), proc(P), naming(N) {}

  void visitBasicBlock(llvm::BasicBlock &bb);
  void visitInstruction(llvm::Instruction &i);

  std::string blockName(const llvm::BasicBlock *bb) const;

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
