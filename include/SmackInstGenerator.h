//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACKINSTVISITOR_H
#define SMACKINSTVISITOR_H

#include "BoogieAst.h"
#include "SmackRep.h"
#include "llvm/Support/InstVisitor.h"
#include <set>

namespace smack {

    class SmackInstGenerator : public llvm::InstVisitor<SmackInstGenerator> {
        
    private:
        SmackRep* rep;
        Procedure& currProc;
        Block *currBlock;
        map<const llvm::BasicBlock*, Block*>& blockMap;
        set<pair<llvm::Function*,int> >& missingDecls;
        int blockNum;
        int varNum;
  
        const Stmt * generateCall(llvm::Function *f, vector<const Expr*> ps, vector<string> rs);

        void generatePhiAssigns(llvm::TerminatorInst& i);
        void generateGotoStmts(vector<pair<const Expr*,string> > target);
        void processInstruction(llvm::Instruction& i);
        void nameInstruction(llvm::Instruction& i);
        
    public:
        SmackInstGenerator(SmackRep* r, Procedure& p,
            map<const llvm::BasicBlock*, Block*>& bm, set<pair<llvm::Function*,int> >& md) 
            : rep(r), currProc(p), blockMap(bm), missingDecls(md),
            blockNum(0), varNum(0) {}

        Block * createBlock();
        void setCurrBlock(Block *b) { currBlock = b; }
        Block * getCurrBlock() { return currBlock; }
        
        string createVar();

        void visitInstruction(llvm::Instruction& i);
        void visitAllocaInst(llvm::AllocaInst& i);
        void visitBranchInst(llvm::BranchInst& i);
        void visitSwitchInst(llvm::SwitchInst& i);
        void visitPHINode(llvm::PHINode& i);
        void visitTruncInst(llvm::TruncInst& i);
        void visitUnreachableInst(llvm::UnreachableInst& i);
        void visitCallInst(llvm::CallInst& i);
        void visitReturnInst(llvm::ReturnInst& i);
        void visitLoadInst(llvm::LoadInst& i);
        void visitStoreInst(llvm::StoreInst& i);
        void visitGetElementPtrInst(llvm::GetElementPtrInst& i);
        void visitICmpInst(llvm::ICmpInst& i);
        void visitZExtInst(llvm::ZExtInst& i);
        void visitSExtInst(llvm::SExtInst& i);
        void visitBitCastInst(llvm::BitCastInst& i);
        void visitBinaryOperator(llvm::BinaryOperator& i);
        void visitPtrToIntInst(llvm::PtrToIntInst& i);
        void visitIntToPtrInst(llvm::IntToPtrInst& i);
        void visitSelectInst(llvm::SelectInst& i);
        void visitAtomicCmpXchgInst(llvm::AtomicCmpXchgInst& i);
    };
}

#endif  /*SMACKINSTVISITOR_H*/
