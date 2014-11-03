//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACKINSTVISITOR_H
#define SMACKINSTVISITOR_H

#include "smack/BoogieAst.h"
#include "smack/SmackRep.h"
#include "smack/Naming.h"
#include "smack/Slicing.h"
#include "llvm/IR/InstVisitor.h"
#include <unordered_set>
#include <set>

namespace smack {

typedef vector<Slice*> Slices;

class SmackInstGenerator : public llvm::InstVisitor<SmackInstGenerator> {

private:
  SmackRep& rep;
  CodeContainer& proc;
  Naming& naming;
  Slices& slices;

  Block* currBlock;
  map<const llvm::BasicBlock*, Block*> blockMap;
  map<const llvm::Value*, string> sourceNames;

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

public:
  void emit(const Stmt* s) {
    // stringstream str;
    // s->print(str);
    // DEBUG(llvm::errs() << "emit:   " << str.str() << "\n");
    currBlock->addStmt(s);
  }

public:
  SmackInstGenerator(SmackRep& R, CodeContainer& P, Naming& N, Slices& S)
    : rep(R), proc(P), naming(N), slices(S) {}

  Slice* getSlice(llvm::Value* V) {
    using namespace llvm;
    if (ConstantInt* CI = dyn_cast<ConstantInt>(V)) {
      uint64_t i = CI->getLimitedValue();
      assert(slices.size() > i && "Did not find expression.");
      return slices[i];
    }
    assert(false && "Unexpected value.");
  }

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
  // TODO implement shufflevector

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
  // TODO implement va_arg
  void visitLandingPadInst(llvm::LandingPadInst& i);
  
  void visitMemCpyInst(llvm::MemCpyInst& i);
  void visitMemSetInst(llvm::MemSetInst& i);
};
}

#endif // SMACKINSTVISITOR_H
