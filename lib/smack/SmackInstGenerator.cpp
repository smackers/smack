//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "SmackInstGenerator.h"
#include "llvm/Support/InstVisitor.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/GraphWriter.h"
#include "llvm/Support/GetElementPtrTypeIterator.h"
#include <sstream>

namespace smack {

    using llvm::errs;
    using namespace std;

    void SmackInstGenerator::processInstruction(llvm::Instruction& inst) {
        DEBUG(errs() << "Inst: " << inst << "\n");
        DEBUG(errs() << "Inst name: " << inst.getName().str() << "\n");
        if (!inst.getType()->isVoidTy()) {
            bool isBool = inst.getType()->isIntegerTy(1);
            if (!inst.hasName())
                inst.setName(isBool ? "$b" : "$p");
            VarDecl *d = new VarDecl(values.asId(&inst), isBool ? "bool" : "$ptr");        
            if (!currProc->hasDecl(d))
                currProc->addDecl(d);
      }
    }

    void SmackInstGenerator::visitInstruction(llvm::Instruction& inst) {
        DEBUG(errs() << "Instruction not handled: " << inst << "\n");
        assert(false && "Instruction not handled");
    }

    void SmackInstGenerator::visitAllocaInst(llvm::AllocaInst& ai) {
        processInstruction(ai);
        unsigned typeSize = values.storageSize(ai.getAllocatedType());
        llvm::Value *arraySize = ai.getArraySize();
        currBlock->addStmt( Stmt::call("$alloca", 
            Expr::fn("$mul", values.asLit(typeSize), values.asLit(arraySize)),
            values.asId(&ai)) );
    }
    
    void SmackInstGenerator::generatePhiAssigns(llvm::TerminatorInst& ti) {        
        llvm::BasicBlock *block = ti.getParent();
        for (unsigned i=0; i<ti.getNumSuccessors(); i++) {
        
            // write to the phi-node variable of the successor
            for (llvm::BasicBlock::iterator
                s = ti.getSuccessor(i)->begin(), e = ti.getSuccessor(i)->end(); 
                s != e && llvm::isa<llvm::PHINode>(s); ++s) {
        
                llvm::PHINode* phi = llvm::cast<llvm::PHINode>(s);
                if (llvm::Value* v = 
                        phi->getIncomingValueForBlock(block)) {

                    processInstruction(*phi);
                    currBlock->addStmt(Stmt::assign(
                        Expr::id(values.asId(phi)), values.asExpr(v)));
                }
            } 
        }
    }
    
    void SmackInstGenerator::generateGotoStmts(vector<pair<Expr*,string> > targets) {

        assert (targets.size() > 0);
        
        if (targets.size() > 1) {
            vector<string> dispatch;
        
            for (unsigned i=0; i<targets.size(); i++) {
                stringstream ss;
                ss << currBlock->getName() << "#C" << i;
                string name = ss.str();
            
                Block *b = new Block(name);
                b->addStmt(Stmt::assume(targets[i].first));
                b->addStmt(Stmt::goto_(targets[i].second));
                currProc->addBlock(b);
                dispatch.push_back(name);
            }

            currBlock->addStmt(Stmt::goto_(dispatch));

        } else
            currBlock->addStmt(Stmt::goto_(targets[0].second));        
    }

    void SmackInstGenerator::visitBranchInst(llvm::BranchInst& bi) {
        processInstruction(bi);
        
        // Collect the list of tarets
        vector<pair<Expr*,string> > targets;
        
        if (bi.getNumSuccessors() == 1) {
            
            // Unconditional branch
            assert (blockMap.count(bi.getSuccessor(0)) != 0);                     
            targets.push_back(make_pair( Expr::lit(true),
                blockMap[bi.getSuccessor(0)]->getName() ));
            
        } else {
            
            // Conditional branch
            assert (bi.getNumSuccessors() == 2);
            assert (blockMap.count(bi.getSuccessor(0)) != 0);
            assert (blockMap.count(bi.getSuccessor(1)) != 0);
            
            Expr *e = values.asExpr(bi.getCondition());
            targets.push_back(make_pair( e,
                blockMap[bi.getSuccessor(0)]->getName() ));
            targets.push_back(make_pair( Expr::not_(e),
                blockMap[bi.getSuccessor(1)]->getName() ));
        }        
        generatePhiAssigns(bi);
        generateGotoStmts(targets);
    }
    
    void SmackInstGenerator::visitSwitchInst(llvm::SwitchInst& si) {
        processInstruction(si);
        
        // Collect the list of tarets
        vector<pair<Expr*,string> > targets;

        Expr *e = values.asExpr(si.getCondition());
        Expr *n = Expr::lit(true);

        for (llvm::SwitchInst::CaseIt
            i = si.case_begin(); i != si.case_begin(); ++i) {
            
            assert (blockMap.count(i.getCaseSuccessor()) != 0);            
            Expr *v = values.asExpr(i.getCaseValue()); 
            targets.push_back(make_pair( Expr::eq(e,v), 
                blockMap[i.getCaseSuccessor()]->getName() ));
            
            // Add the negation of this case to the default case
            n = Expr::and_(n,Expr::neq(e,v));
        }

        // The default case
        assert (blockMap.count(si.getDefaultDest()) != 0);
        targets.push_back(make_pair( n, 
            blockMap[si.getDefaultDest()]->getName() ));

        generatePhiAssigns(si);
        generateGotoStmts(targets);
    }

    void SmackInstGenerator::visitPHINode(llvm::PHINode& phi) {
        // NOTE: this is really a No-Op, since assignments to the phi nodes
        // are handled in the translation of branch/switch instructions.        
        processInstruction(phi);  
    }

    void SmackInstGenerator::visitTruncInst(llvm::TruncInst& ti) {
        processInstruction(ti);
    }  

    void SmackInstGenerator::visitUnreachableInst(llvm::UnreachableInst& ii) {
        processInstruction(ii);
    }  

    // TODO Should we put this DEBUG info back in ?
    // void SmackInstGenerator::processIndirectCall(CallInst& ci) {
        // DEBUG(errs() << "Called value: " << *calledValue << "\n");
        // DEBUG(errs() << "Called value type: " << *calledValueType << "\n");
        // DEBUG(errs() << "Called function type: " << *calledFuncType << "\n");


    // TODO When will we revive the DSA code ?
    // #ifdef USE_DSA
    //     CallSite callSite = CallSite::get(&ci);
    //     if (ci.getCalledFunction() != NULL) {
    //       Function* calledFunction = ci.getCalledFunction();
    //       module->addCalledProcedure(calledFunction->getNameStr());
    //       CalledFunction* calledFunc = stmt->addCalledFunction(calledFunction);
    // 
    //       if ((Common::memoryType == DSA_INDEXED || Common::memoryType == DSA_SPLIT) &&
    //           tdDataStructures->hasDSGraph(*calledFunction)) {
    //         generateMemoryPairings(callSite, calledFunction, calledFunc);
    //       }
    //     } else {
    //       for (vector<const Function*>::iterator i = callTargetFinder->begin(callSite),
    //           ei = callTargetFinder->end(callSite); i != ei; ++i) {
    //         const Function* calledFunction = *i;
    //         module->addCalledProcedure(calledFunction->getNameStr());
    //         if (ci.getCalledValue()->getType() == calledFunction->getType()) {
    //           CalledFunction* calledFunc = stmt->addCalledFunction(calledFunction);
    // 
    //           if ((Common::memoryType == DSA_INDEXED || Common::memoryType == DSA_SPLIT) &&
    //               tdDataStructures->hasDSGraph(*calledFunction)) {
    //             generateMemoryPairings(callSite, calledFunction, calledFunc);
    //           }
    //         }
    //       }
    //     }
    // #endif
    // }

    // TODO Does this function belong here, or in "Values" ?
    Stmt * SmackInstGenerator::generateCall(
        llvm::Function *f, vector<Expr*> args, vector<string> rets ) {
        
        string name = values.asFnId(f);

        // TODO we might instead assume that there are no llvm.dbg symbols
        // having run the -strip-debug-declare before.
        if (name.find("llvm.dbg.") == 0) 
            // a "skip" statement..
            return Stmt::assume(Expr::lit(true));

        else if (name == "__SMACK_assert") {
            assert (args.size() == 1 && rets.size() == 0);
            return Stmt::assert_(Expr::neq(
                args[0], 
                Expr::fn("$ptr",Expr::id("$NULL"),values.asLit((unsigned)0))));

        } else if (name == "__SMACK_assume") {
            assert (args.size() == 1 && rets.size() == 0);
            return Stmt::assume(Expr::neq(
                args[0], 
                Expr::fn("$ptr",Expr::id("$NULL"),values.asLit((unsigned)0))));
        
        } else if (name == "__SMACK_record_int") {
            assert (args.size() == 1 && rets.size() == 0);
            return Stmt::call(name,Expr::fn("$off",args[0]));
        
        } else if (name == "__SMACK_record_obj") {
            assert (args.size() == 1 && rets.size() == 0);
            return Stmt::call(name,Expr::fn("$obj",args[0]));
        
        } else if (name == "__SMACK_record_ptr") {
            assert (args.size() == 1 && rets.size() == 0);
            return Stmt::call(name,args[0]);

        } else if (name == "malloc") {
            assert (args.size() == 1);
            return Stmt::call("$malloc", Expr::fn("$off",args[0]), rets[0]);

        } else if (name == "free") {
            assert(args.size() == 1);
            return Stmt::call("$free",args[0]);
        
        } else if (f->isVarArg() && args.size() > 0) {
            // Handle variable argument functions
            
            // TODO What to do about this assert ?

            // assert( args.size() <= 5 
            // && "Currently only up to 5 var arg parameters are supported" );
            
            // TODO I would treat it as a warning.. the only bad thing that
            // might happen is that we didn't have a corresponding Boogie
            // function in our prelude.
            
            // if (args.size() <= 5)
            // WARN("Currently only up to 5 var arg parameters are supported (?)");

            stringstream ss;
            ss << name << "#" << args.size();
            name = ss.str();
            return Stmt::call(name, args, rets);

        } else {
            return Stmt::call(name, args, rets);
        }
    }

    // Counter for unique block names used for function pointer call dispatch.
    int fpcNum = 0;

    void SmackInstGenerator::visitCallInst(llvm::CallInst& ci) {
        processInstruction(ci);
        
        if (ci.isInlineAsm()) {
            
            // TODO do something / this is UNSOUND.
            
            // WARN("UNSOUNDLY ignoring inline asm call.")
            currBlock->addStmt(Stmt::assume(Expr::lit(true)));
            return;
        }

        vector<Expr*> args;
        for (unsigned i=0; i<ci.getNumOperands()-1; i++)
            args.push_back(values.asExpr(ci.getOperand(i)));

        vector<string> rets;
        if (!ci.getType()->isVoidTy())
            rets.push_back(values.asId(&ci));
    
        if (llvm::Function* f = ci.getCalledFunction())
            currBlock->addStmt( generateCall(f,args,rets) );

        else {
            // function pointer call...
            vector<llvm::Function*> fs;
    
            // Collect the list of possible function calls
            llvm::Value *c = ci.getCalledValue();
            llvm::Type *t = c->getType();
            assert( t->isPointerTy() && "Indirect call value type must be pointer");
            t = t->getPointerElementType();
            llvm::Module *m = ci.getParent()->getParent()->getParent();
            for (llvm::Module::iterator f = m->begin(), e = m->end(); f != e; ++f)
                if (f->getFunctionType() == t)
                    fs.push_back(f);
        
            if (fs.size() == 1)
                // Q: is this case really possible?
                currBlock->addStmt(generateCall(fs[0],args,rets));
    
            else if (fs.size() > 1) {
                string tgt;
                stringstream ss(tgt);
                ss << "$fp#" << fpcNum++;
                tgt = ss.str();
                Block *tail = new Block(tgt);
                vector<string> targets;            
            
                // Create a sequence of dispatch blocks, one for each call.
                for (unsigned i=0; i<fs.size(); i++) {                
                    stringstream ss;
                    ss << tgt << "#D" << i;
                    string name = ss.str();
                    
                    Block *disp = new Block(name);
                    targets.push_back(name);

                    disp->addStmt(Stmt::assume(
                        Expr::eq(values.asExpr(c),Expr::id(values.asId(fs[i])))));
                    disp->addStmt(generateCall(fs[i],args,rets));
                    disp->addStmt(Stmt::goto_(tgt));
                    currProc->addBlock(disp);
                }

                // Jump to the dispatch blocks.
                currBlock->addStmt(Stmt::goto_(targets));

                // Update the current block for subsequent visits.
                currBlock = tail;
                currProc->addBlock(tail);
        
            } else {
                // In the worst case, we have no idea what function may have
                // been called...
                
                // assert (false && "unable to resolve function call...");
            
                // TODO do something / this is UNSOUND.
                
                // For the moment, let's UNSOUNDLY just ignore this call.
                // WARN("UNSOUNDLY ignoring indeterminate call.")
                currBlock->addStmt(Stmt::assume(Expr::lit(true)));
            }
        }
    }

    void SmackInstGenerator::visitReturnInst(llvm::ReturnInst& ri) {
      processInstruction(ri);
  
      if (llvm::Value *v = ri.getReturnValue())
        currBlock->addStmt( Stmt::assign(Expr::id("$r"), values.asExpr(v)) );
  
      currBlock->addStmt( Stmt::return_() );
    }

    void SmackInstGenerator::visitLoadInst(llvm::LoadInst& li) {
      processInstruction(li);  
      assert(li.hasName() && "Variable has to have a name");
      currBlock->addStmt(Stmt::assign(values.asExpr(&li),
          Expr::sel(Expr::id("$Mem"), values.asExpr(li.getPointerOperand()))));
    }

    void SmackInstGenerator::visitStoreInst(llvm::StoreInst& si) {
        processInstruction(si);
        currBlock->addStmt(Stmt::assign(
            Expr::sel(Expr::id("$Mem"), values.asExpr(si.getPointerOperand())), 
            values.asExpr(si.getOperand(0))));
    }

    void SmackInstGenerator::visitGetElementPtrInst(llvm::GetElementPtrInst& gepi) {
        processInstruction(gepi);

        vector<llvm::Value*> ps;
        vector<llvm::Type*> ts;
        llvm::gep_type_iterator typeI = gep_type_begin(gepi);
        for (unsigned i=1; i<gepi.getNumOperands(); i++, ++typeI) {
            ps.push_back(gepi.getOperand(i));
            ts.push_back(*typeI);
        }
        currBlock->addStmt(Stmt::assign(values.asExpr(&gepi), 
            values.gepAsExpr(gepi.getPointerOperand(),ps,ts)));
    }

    void SmackInstGenerator::visitICmpInst(llvm::ICmpInst& ci) {
        processInstruction(ci);
        Expr *l = values.asExpr(ci.getOperand(0)),
            *r = values.asExpr(ci.getOperand(1));
        
        Expr *e = NULL;
        string o;
    
        switch (ci.getPredicate()) {
            using llvm::ICmpInst;
            case ICmpInst::ICMP_EQ: e = Expr::eq(l,r); break;
            case ICmpInst::ICMP_NE: e = Expr::neq(l,r); break;
            case ICmpInst::ICMP_SGE: o = "$sge"; break;
            case ICmpInst::ICMP_UGE: o = "$uge"; break;
            case ICmpInst::ICMP_SLE: o = "$sle"; break;
            case ICmpInst::ICMP_ULE: o = "$ule"; break;
            case ICmpInst::ICMP_SLT: o = "$slt"; break;
            case ICmpInst::ICMP_ULT: o = "$ult"; break;
            case ICmpInst::ICMP_SGT: o = "$sgt"; break;
            case ICmpInst::ICMP_UGT: o = "$ugt"; break;
            default:
            assert( false && "unexpected predicate." );
        }
        if (e == NULL) e = Expr::fn(o, Expr::fn("$off",l), Expr::fn("$off",r));        
        currBlock->addStmt(Stmt::assign(values.asExpr(&ci),e));
    }

    void SmackInstGenerator::visitZExtInst(llvm::ZExtInst& ci) {
        processInstruction(ci);
        
        Expr *e = values.asExpr(ci.getOperand(0));
        if (ci.getSrcTy()->isIntegerTy() 
            && ci.getSrcTy()->getPrimitiveSizeInBits() == 1)
            e = Expr::fn("$b2p",e);
        currBlock->addStmt(Stmt::assign(values.asExpr(&ci),e));
    }

    void SmackInstGenerator::visitSExtInst(llvm::SExtInst& ci) {
        processInstruction(ci);
        
        Expr *e = values.asExpr(ci.getOperand(0));
        if (ci.getSrcTy()->isIntegerTy() 
            && ci.getSrcTy()->getPrimitiveSizeInBits() == 1)
            e = Expr::fn("$b2p",e);
        currBlock->addStmt(Stmt::assign(values.asExpr(&ci), e));
    }

    void SmackInstGenerator::visitBitCastInst(llvm::BitCastInst& ci) {

        // TODO: currently this is a noop instruction
        processInstruction(ci);
        currBlock->addStmt(Stmt::assign(
            values.asExpr(&ci), values.asExpr(ci.getOperand(0))));
    }

    void SmackInstGenerator::visitBinaryOperator(llvm::BinaryOperator& bo) {
        processInstruction(bo);
      
        string op;
        switch (bo.getOpcode()) {
            using llvm::Instruction;
            case Instruction::Add: op = "$add"; break;
            case Instruction::Sub: op = "$sub"; break;
            case Instruction::Mul: op = "$mul"; break;
            case Instruction::SDiv: op = "$sdiv"; break;
            case Instruction::UDiv: op = "$udiv"; break;
            case Instruction::SRem: op = "$srem"; break;
            case Instruction::URem: op = "$urem"; break;
            case Instruction::And: op = "$and"; break;
            case Instruction::Or: op = "$or"; break;
            case Instruction::Xor: op = "$xor"; break;
            case Instruction::LShr: op = "$LShr"; break;
            case Instruction::AShr: op = "$AShr"; break;
            case Instruction::Shl: op = "$Shl"; break;
            default: assert( false && "predicate not supported" );
        }
        Expr 
            *left = values.asIntExpr(bo.getOperand(0)),
            *right = values.asIntExpr(bo.getOperand(1));
        Expr *e = Expr::fn(op, left, right);
        Expr *f = bo.getType()->isIntegerTy(1)
            ? Expr::fn("$i2b", e)
            : Expr::fn("$ptr", Expr::id("$NULL"), e);
        currBlock->addStmt(Stmt::assign(values.asExpr(&bo), f));
    }

    // TODO Maybe we should reinstate this legacy code..

    // void SmackInstGenerator::visitAtomicCmpXchgInst(AtomicCmpXchgInst &I) {
    //   processInstruction(I);
    //   Expr 
    //     *res = new VarExpr(&I),
    //     *ndvar = new VarExpr("$ndvar"),
    //     *b2p = new VarExpr("$b2p"),
    //     *fst = new MemExpr(visitValue(I.getOperand(0)), Memory::create()),
    //     *snd = visitValue(I.getOperand(1)),
    //     *thd = visitValue(I.getOperand(2)),
    //     *same = new BinExpr(res,Expr::EqOp,snd),
    //     *diff = new BinExpr(res,Expr::NeqOp,snd),
    //     *pos = new BinExpr(ndvar,Expr::EqOp,thd),
    //     *neg = new BinExpr(ndvar,Expr::EqOp,res);
    //   FunExpr
    //     *po1 = new FunExpr(b2p),
    //     *po2 = new FunExpr(b2p);
    //   
    //   po1->addArgument(new BinExpr(diff,Expr::OrOp,pos));
    //   po2->addArgument(new BinExpr(same,Expr::OrOp,neg));
    //   
    //   block->addInstruction( new AssignStmt(&I, res, fst) );
    //   block->addInstruction( new HavocStmt(&I, ndvar) );
    //   block->addInstruction( new AssumeStmt(&I, po1) );
    //   block->addInstruction( new AssumeStmt(&I, po2) );
    //   block->addInstruction( new AssignStmt(&I, fst, ndvar) );
    // }

    void SmackInstGenerator::visitPtrToIntInst(llvm::PtrToIntInst& i) {
        processInstruction(i);
        currBlock->addStmt(Stmt::assign(values.asExpr(&i),
            Expr::fn("$p2i",values.asExpr(i.getOperand(0)))));
    }

    void SmackInstGenerator::visitIntToPtrInst(llvm::IntToPtrInst& i) {
      processInstruction(i);
        currBlock->addStmt(Stmt::assign(values.asExpr(&i),
            Expr::fn("$i2p",values.asExpr(i.getOperand(0)))));
    }

    void SmackInstGenerator::visitSelectInst(llvm::SelectInst& i) {
        processInstruction(i);
        string x = values.asId(&i);
        Expr 
            *c = values.asExpr(i.getOperand(0)),
            *v1 = values.asExpr(i.getOperand(1)),
            *v2 = values.asExpr(i.getOperand(2));

        currBlock->addStmt(Stmt::havoc(x));
        currBlock->addStmt(Stmt::assume(Expr::and_(
            Expr::impl(c,Expr::eq(Expr::id(x),v1)), 
            Expr::impl(Expr::not_(c),Expr::eq(Expr::id(x),v2))
        )));
    }

} // namespace smack
