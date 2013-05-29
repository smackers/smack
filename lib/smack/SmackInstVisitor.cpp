//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "SmackInstVisitor.h"
#include "Utils.h"
#include "BplPrintUtils.h"
#include <sstream>

using namespace smack;

const int width = 0;

Expr * lit(Value *v) {
    if (const ConstantInt* ci = dyn_cast<ConstantInt>(v)) {
        if (ci->getBitWidth() == 1)
            return Expr::lit(!ci->isZero());

        uint64_t val = ci->getLimitedValue();
       if (ci->isNegative()) 
           return Expr::fn("$sub", Expr::lit(0,width), Expr::lit(-val,width));
       else
           return Expr::lit(val,width);
        
    } else if (isa<ConstantPointerNull>(v))
        return Expr::lit(0,width);
        
     else
        assert( false && "value type not supported" );
 }

Expr * lit(unsigned v) {
    // TODO why doesn't this one do the thing with negative as well?
    return Expr::lit(v,width);
}

string id(Value *v) {
    if (v->hasName()) {
        if (isa<Function>(v)) {
            stringstream ss;
            ss << smack::strip(v->getName().str()) << "#ptr";
            return ss.str();
        } else 
            return smack::translateName(v);
    } else
        assert( false && "expected named value." );
}

string fun(Value *v) {
    if (v->hasName())
        return smack::strip(v->getName().str());
    else
        assert( false && "expected named value." );
}

Expr * SmackInstVisitor::expr(Value *v) {
    if (v->hasName())
        return Expr::id(id(v));        
        
    else if (Constant* constant = dyn_cast<Constant>(v)) {

        if (ConstantExpr* constantExpr = dyn_cast<ConstantExpr>(constant)) {
            
            if (constantExpr->getOpcode() == Instruction::GetElementPtr) {

                unsigned n = constantExpr->getNumOperands();
                Value* pv = constantExpr->getOperand(0);
                Expr *p = expr(pv);

                Type* type = pv->getType();
                gep_type_iterator typeI = gep_type_begin(constantExpr);
                
                for (unsigned i = 1; i < n; i++, ++typeI) {
                    
                    Constant* idx = constantExpr->getOperand(i);
                    
                    if (StructType* structType = dyn_cast<StructType>(*typeI)) {
                        
                        assert( idx->getType()->isIntegerTy() 
                            && idx->getType()->getPrimitiveSizeInBits() == 32 
                            && "Illegal struct idx" );

                        // Get structure layout information...
                        const StructLayout* layout = targetData->getStructLayout(structType);
                        unsigned fieldNo = cast<ConstantInt>(idx)->getZExtValue();

                        // Add in the offset, as calculated by the      
                        // structure layout info...
                        p = Expr::fn("$pa", p, 
                            Expr::lit((int) layout->getElementOffset(fieldNo)),
                            Expr::lit(1));

                        // Update type to refer to current element
                        type = structType->getElementType(fieldNo);
                        
                    } else {
                        // Update type to refer to current element
                        type = cast<SequentialType>(type)->getElementType();
                        p = Expr::fn("$pa", p, expr(idx), 
                            Expr::lit((int) targetData->getTypeStoreSize(type)));
                    }
                }
                return p;
                
            } else if (constantExpr->getOpcode() == Instruction::BitCast)

                  // TODO: currently this is a noop instruction
                  return expr( constantExpr->getOperand(0) );
                  
            else if (constantExpr->getOpcode() == Instruction::IntToPtr)
                return Expr::id("$UNDEF");

            else
                assert( false && "constant expression of this type not supported" );

        } else if (ConstantInt* ci = dyn_cast<ConstantInt>(constant)) {

            if (ci->getBitWidth() == 1)
                return Expr::lit(!ci->isZero());
            else
                return Expr::fn("$ptr", Expr::id("$NULL"), lit(ci));

        } else if (constant->isNullValue())
            return Expr::fn("$ptr", Expr::id("$NULL"), Expr::lit(0));
            
        else if (isa<UndefValue>(constant))
            return Expr::id("$UNDEF");

        else
            assert( false && "this type of constant not supported" );
            
    } else {
        assert( false && "value of this type not supported" );
    }
    
}

void SmackInstVisitor::visitInstruction(Instruction& inst) {
  DEBUG(errs() << "Instruction not handled: " << inst << "\n");
  assert(false && "Instruction not handled");
}

void SmackInstVisitor::processInstruction(Instruction& inst) {
    DEBUG(errs() << "Inst: " << inst << "\n");
    DEBUG(errs() << "Inst name: " << inst.getName().str() << "\n");
    if (inst.getType()->getTypeID() != Type::VoidTyID) {
        bool isBool = inst.getType()->isIntegerTy(1);
        if (!inst.hasName())
            inst.setName(isBool ? "$b" : "$p");
        currProc->addDecl(new VarDecl(
            translateName(&inst),
            isBool ? "bool" : "$ptr"
        ));
  }
}

void SmackInstVisitor::visitAllocaInst(AllocaInst& ai) {
    processInstruction(ai);

    Type* allocType = ai.getAllocatedType();
    unsigned typeSize = targetData->getTypeStoreSize(allocType);
    Value *arraySize = ai.getArraySize();
    currBlock->addStmt( Stmt::call("$alloca", 
        Expr::fn("$mul", lit(typeSize), lit(arraySize)),
        id(&ai)) );
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
//   const Value* calledValue = ci.getCalledValue();
//   DEBUG(errs() << "Called value: " << *calledValue << "\n");
//   Type* calledValueType = calledValue->getType();
//   DEBUG(errs() << "Called value type: " << *calledValueType << "\n");
//   assert(calledValueType->isPointerTy() && "Indirect call value type has to be a pointer");
//   Type* calledFuncType = calledValueType->getPointerElementType();
//   DEBUG(errs() << "Called function type: " << *calledFuncType << "\n");
// 
//   CallStmt* stmt = new CallStmt(&ci);
//   VarExpr* functionPointer = new VarExpr(calledValue);
//   stmt->setFunctionPointer(functionPointer);
// 
//   Module* module = ci.getParent()->getParent()->getParent();
//   for (Module::iterator func = module->begin(), e = module->end(); func != e; ++func) {
//     DEBUG(errs() << "Function type: " << *func->getFunctionType() << "\n");
//     if (func->getFunctionType() == calledFuncType) {
//       DEBUG(errs() << "Matching called function type: " << *func << "\n");
//       stmt->addCalledFunction(func);
//     }
//   }
// //  assert(false && "Indirect function calls currently not supported");
// 
//   if (ci.getType()->getTypeID() != Type::VoidTyID) {
//     VarExpr* returnVar = new VarExpr(&ci);
//     stmt->setReturnVar(returnVar);
//   }
// 
//   for (unsigned i = 0, e = ci.getNumOperands() - 1; i < e; ++i) {
//     Expr* param = visitValue(ci.getOperand(i));
//     stmt->addParam(param);
//   }
// 
//   block->addInstruction(stmt);
// 
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

void SmackInstVisitor::generateCall(
    string name, vector<Expr*> args, vector<string> rets ) {

    if (name.find("llvm.dbg.") == 0) 
        ;

    else if (name == "__SMACK_assert") {
        assert (args.size() == 1 && rets.size() == 0);
        currBlock->addStmt(Stmt::assert_(args[0]));

    } else if (name == "__SMACK_assume") {
        assert (args.size() == 1 && rets.size() == 0);
        currBlock->addStmt(Stmt::assume(args[0]));

    } else if (name == "malloc") {
        assert (args.size() == 1);
        currBlock->addStmt(Stmt::call("$malloc", args[0], rets[0]));

    } else if (name == "free") {
        assert(args.size() == 1);
        currBlock->addStmt(Stmt::call("$free",args[0]));

    } else
        currBlock->addStmt(Stmt::call(name, args, rets));    
}

void SmackInstVisitor::visitCallInst(CallInst& ci) {
    processInstruction(ci);

    if (Function* f = ci.getCalledFunction()) {
        string name = fun(f);
        vector<Expr*> args;
        vector<string> rets;
    
        for (unsigned i=0; i<ci.getNumOperands()-1; i++)
            args.push_back(expr(ci.getOperand(i)));

        if (!ci.getType()->isVoidTy())
            rets.push_back(id(&ci));

        generateCall(name,args,rets);

    } else {
        // function pointer call
        assert( false && "function pointer call" );
    }
}

void SmackInstVisitor::visitReturnInst(ReturnInst& ri) {
  processInstruction(ri);
  
  if (Value *v = ri.getReturnValue())
    currBlock->addStmt( Stmt::assign(Expr::id("$r"), expr(v)) );
  
  currBlock->addStmt( Stmt::return_() );
}

void SmackInstVisitor::visitLoadInst(LoadInst& li) {
  processInstruction(li);  
  assert(li.hasName() && "Variable has to have a name");
  currBlock->addStmt(Stmt::assign(expr(&li),
      Expr::sel(Expr::id("$Mem"), expr(li.getPointerOperand()))));
}

void SmackInstVisitor::visitStoreInst(StoreInst& si) {
    processInstruction(si);
    currBlock->addStmt(Stmt::assign(
        Expr::sel(Expr::id("$Mem"), expr(si.getPointerOperand())), 
        expr(si.getOperand(0))));
}

void SmackInstVisitor::visitGetElementPtrInst(GetElementPtrInst& gepi) {
    processInstruction(gepi);

    // TODO Lots of duplication with the expr() procedure here..

    Expr *p = expr(gepi.getPointerOperand());
    unsigned n = gepi.getNumOperands();

    gep_type_iterator typeI = gep_type_begin(gepi);
    
    for (unsigned i=1; i<n; i++, ++typeI) {        
        Value* idx = gepi.getOperand(i);        
        if (StructType* structType = dyn_cast<StructType>(*typeI)) {
            
            assert( idx->getType()->isIntegerTy() 
                && idx->getType()->getPrimitiveSizeInBits() == 32 
                && "Illegal struct idx" );

            // Get structure layout information...
            const StructLayout* layout = targetData->getStructLayout(structType);
            unsigned fieldNo = cast<ConstantInt>(idx)->getZExtValue();

            // Add in the offset, as calculated by the      
            // structure layout info...
            p = Expr::fn("$pa", p, 
                Expr::lit((int) layout->getElementOffset(fieldNo)),
                Expr::lit(1));

        } else {
            // Update type to refer to current element
            Type *type = cast<SequentialType>(*typeI)->getElementType();
            p = Expr::fn("$pa", p, expr(idx), 
                Expr::lit((int) targetData->getTypeStoreSize(type)));
        }
    }
    
    currBlock->addStmt(Stmt::assign(expr(&gepi), p));
}

void SmackInstVisitor::visitICmpInst(ICmpInst& ci) {
    processInstruction(ci);
    Expr *l = expr(ci.getOperand(0)),
        *r = expr(ci.getOperand(1));
        
    Expr *e;
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
    if (!e) e = Expr::fn(o, Expr::fn("$off",l), Expr::fn("$off",r));        
    currBlock->addStmt(Stmt::assign(expr(&ci),e));
}

void SmackInstVisitor::visitZExtInst(ZExtInst& ci) {
    processInstruction(ci);
        
    Expr *e = expr(ci.getOperand(0));
    if (ci.getSrcTy()->isIntegerTy() 
        && ci.getSrcTy()->getPrimitiveSizeInBits() == 1)
        e = Expr::fn("$b2p",e);
    currBlock->addStmt(Stmt::assign(expr(&ci),e));
}

void SmackInstVisitor::visitSExtInst(SExtInst& ci) {
    processInstruction(ci);
        
    Expr *e = expr(ci.getOperand(0));
    if (ci.getSrcTy()->isIntegerTy() 
        && ci.getSrcTy()->getPrimitiveSizeInBits() == 1)
        e = Expr::fn("$b2p",e);
    currBlock->addStmt(Stmt::assign(expr(&ci), e));
}

void SmackInstVisitor::visitBitCastInst(BitCastInst& ci) {

    // TODO: currently this is a noop instruction
    processInstruction(ci);
    currBlock->addStmt(Stmt::assign(expr(&ci), expr(ci.getOperand(0))));
}

Expr * SmackInstVisitor::operand(Value *o) {
    return Expr::fn( (o->getType()->isIntegerTy(1) ? "$b2i" : "$off"), expr(o));
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
        *left = operand(bo.getOperand(0)),
        *right = operand(bo.getOperand(1));
    Expr *e = Expr::fn(op, left, right);
    Expr *f = bo.getType()->isIntegerTy(1)
        ? Expr::fn("$i2b", e)
        : Expr::fn("$ptr", Expr::id("$NULL"), e);
    currBlock->addStmt(Stmt::assign(expr(&bo), f));
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
