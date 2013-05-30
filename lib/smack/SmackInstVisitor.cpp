//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "SmackInstVisitor.h"
#include "llvm/Support/InstVisitor.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/GraphWriter.h"
#include "llvm/Support/GetElementPtrTypeIterator.h"
#include <sstream>

using namespace smack;

void SmackInstVisitor::processInstruction(Instruction& inst) {
    DEBUG(errs() << "Inst: " << inst << "\n");
    DEBUG(errs() << "Inst name: " << inst.getName().str() << "\n");
    if (inst.getType()->getTypeID() != Type::VoidTyID) {
        bool isBool = inst.getType()->isIntegerTy(1);
        if (!inst.hasName())
            inst.setName(isBool ? "$b" : "$p");
        VarDecl *d = new VarDecl(values.id(&inst), isBool ? "bool" : "$ptr");        
        if (!currProc->hasDecl(d))
            currProc->addDecl(d);
  }
}

void SmackInstVisitor::visitInstruction(Instruction& inst) {
  DEBUG(errs() << "Instruction not handled: " << inst << "\n");
  assert(false && "Instruction not handled");
}

void SmackInstVisitor::visitAllocaInst(AllocaInst& ai) {
    processInstruction(ai);
    unsigned typeSize = values.storageSize(ai.getAllocatedType());
    Value *arraySize = ai.getArraySize();
    currBlock->addStmt( Stmt::call("$alloca", 
        Expr::fn("$mul", values.lit(typeSize), values.lit(arraySize)),
        values.id(&ai)) );
}

void SmackInstVisitor::visitBranchInst(BranchInst& bi) {
  processInstruction(bi);
}

void SmackInstVisitor::visitPHINode(PHINode& phi) {
  processInstruction(phi);  
}

void SmackInstVisitor::visitTruncInst(TruncInst& ti) {
  processInstruction(ti);
}  

void SmackInstVisitor::visitUnreachableInst(UnreachableInst& ii) {
  processInstruction(ii);
}  

// void SmackInstVisitor::processIndirectCall(CallInst& ci) {
    // DEBUG(errs() << "Called value: " << *calledValue << "\n");
    // DEBUG(errs() << "Called value type: " << *calledValueType << "\n");
    // DEBUG(errs() << "Called function type: " << *calledFuncType << "\n");


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

Stmt * SmackInstVisitor::generateCall(
    Function *f, vector<Expr*> args, vector<string> rets ) {
        
    string name = values.fun(f);

    if (name.find("llvm.dbg.") == 0) 
        // a "skip" statement..
        return Stmt::assume(Expr::lit(true));

    else if (name == "__SMACK_assert") {
        assert (args.size() == 1 && rets.size() == 0);
        return Stmt::assert_(Expr::neq(
            args[0], Expr::fn("$ptr",Expr::id("$NULL"),values.lit((unsigned)0))));

    } else if (name == "__SMACK_assume") {
        assert (args.size() == 1 && rets.size() == 0);
        return Stmt::assume(Expr::neq(
            args[0], Expr::fn("$ptr",Expr::id("$NULL"),values.lit((unsigned)0))));
        
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
        assert( args.size() <= 5 
            && "Currently only up to 5 var arg parameters are supported" );
        stringstream ss;
        ss << name << "#" << args.size();
        name = ss.str();
        return Stmt::call(name, args, rets);

    } else {
        return Stmt::call(name, args, rets);
    }
}

void SmackInstVisitor::visitCallInst(CallInst& ci) {
    processInstruction(ci);

    vector<Expr*> args;
    for (unsigned i=0; i<ci.getNumOperands()-1; i++)
        args.push_back(values.expr(ci.getOperand(i)));

    vector<string> rets;
    if (!ci.getType()->isVoidTy())
        rets.push_back(values.id(&ci));
    
    if (Function* f = ci.getCalledFunction())
        currBlock->addStmt( generateCall(f,args,rets) );

    else {
        // function pointer call...
        vector<llvm::Function*> fs;
    
        // Collect the list of possible function calls
        llvm::Type *t = ci.getCalledValue()->getType();
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
            assert (false && "TODO : implement function pointer dispatch.");
            for (unsigned i=0; i<fs.size(); i++) {
                // ...
            }
        
        } else
            assert (false && "unable to resolve function call...");
    }
}

void SmackInstVisitor::visitReturnInst(ReturnInst& ri) {
  processInstruction(ri);
  
  if (Value *v = ri.getReturnValue())
    currBlock->addStmt( Stmt::assign(Expr::id("$r"), values.expr(v)) );
  
  currBlock->addStmt( Stmt::return_() );
}

void SmackInstVisitor::visitLoadInst(LoadInst& li) {
  processInstruction(li);  
  assert(li.hasName() && "Variable has to have a name");
  currBlock->addStmt(Stmt::assign(values.expr(&li),
      Expr::sel(Expr::id("$Mem"), values.expr(li.getPointerOperand()))));
}

void SmackInstVisitor::visitStoreInst(StoreInst& si) {
    processInstruction(si);
    currBlock->addStmt(Stmt::assign(
        Expr::sel(Expr::id("$Mem"), values.expr(si.getPointerOperand())), 
        values.expr(si.getOperand(0))));
}

void SmackInstVisitor::visitGetElementPtrInst(GetElementPtrInst& gepi) {
    processInstruction(gepi);

    // TODO Lots of duplication with the values.expr() procedure here..

    Expr *p = values.expr(gepi.getPointerOperand());
    unsigned n = gepi.getNumOperands();

    gep_type_iterator typeI = gep_type_begin(gepi);
    
    for (unsigned i=1; i<n; i++, ++typeI) {        
        Value* idx = gepi.getOperand(i);        
        if (StructType* structType = dyn_cast<StructType>(*typeI)) {
            
            assert( idx->getType()->isIntegerTy() 
                && idx->getType()->getPrimitiveSizeInBits() == 32 
                && "Illegal struct idx" );

            // Get structure layout information...
            unsigned fieldNo = cast<ConstantInt>(idx)->getZExtValue();

            // Add in the offset, as calculated by the      
            // structure layout info...
            p = Expr::fn("$pa", p, 
                Expr::lit((int) values.fieldOffset(structType,fieldNo)),
                Expr::lit(1));

        } else {
            // Update type to refer to current element
            Type *type = cast<SequentialType>(*typeI)->getElementType();
            p = Expr::fn("$pa", p, values.lit(idx),
                Expr::lit((int) values.storageSize(type)));
        }
    }
    
    currBlock->addStmt(Stmt::assign(values.expr(&gepi), p));
}

void SmackInstVisitor::visitICmpInst(ICmpInst& ci) {
    processInstruction(ci);
    Expr *l = values.expr(ci.getOperand(0)),
        *r = values.expr(ci.getOperand(1));
        
    Expr *e = NULL;
    string o;
    
    switch (ci.getPredicate()) {
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
    currBlock->addStmt(Stmt::assign(values.expr(&ci),e));
}

void SmackInstVisitor::visitZExtInst(ZExtInst& ci) {
    processInstruction(ci);
        
    Expr *e = values.expr(ci.getOperand(0));
    if (ci.getSrcTy()->isIntegerTy() 
        && ci.getSrcTy()->getPrimitiveSizeInBits() == 1)
        e = Expr::fn("$b2p",e);
    currBlock->addStmt(Stmt::assign(values.expr(&ci),e));
}

void SmackInstVisitor::visitSExtInst(SExtInst& ci) {
    processInstruction(ci);
        
    Expr *e = values.expr(ci.getOperand(0));
    if (ci.getSrcTy()->isIntegerTy() 
        && ci.getSrcTy()->getPrimitiveSizeInBits() == 1)
        e = Expr::fn("$b2p",e);
    currBlock->addStmt(Stmt::assign(values.expr(&ci), e));
}

void SmackInstVisitor::visitBitCastInst(BitCastInst& ci) {

    // TODO: currently this is a noop instruction
    processInstruction(ci);
    currBlock->addStmt(Stmt::assign(values.expr(&ci), values.expr(ci.getOperand(0))));
}

void SmackInstVisitor::visitBinaryOperator(BinaryOperator& bo) {
    processInstruction(bo);
      
    string op;
    switch (bo.getOpcode()) {
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
        *left = values.integer(bo.getOperand(0)),
        *right = values.integer(bo.getOperand(1));
    Expr *e = Expr::fn(op, left, right);
    Expr *f = bo.getType()->isIntegerTy(1)
        ? Expr::fn("$i2b", e)
        : Expr::fn("$ptr", Expr::id("$NULL"), e);
    currBlock->addStmt(Stmt::assign(values.expr(&bo), f));
}

// void SmackInstVisitor::visitAtomicCmpXchgInst(AtomicCmpXchgInst &I) {
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

// void SmackInstVisitor::visitPtrToIntInst(PtrToIntInst &I) {
//   processInstruction(I);
//   Expr *dest = new VarExpr(&I);
//   FunExpr *src = new FunExpr(new VarExpr("$p2i"));
//   src->addArgument( visitValue(I.getOperand(0)) );
//   block->addInstruction( new AssignStmt(&I, dest, src) );
// }
