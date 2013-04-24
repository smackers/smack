//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "SmackInstVisitor.h"

using namespace smack;

Expr* SmackInstVisitor::visitValue(Value* value) {
  Expr* valExpr = NULL;

  if (value->hasName()) {
    if (isa<Function>(value)) {
      // function pointer
      DEBUG(errs() << "Value not handled: " << *value << "\n");
      assert(false && "Constant expression of this type not supported");
      valExpr = new UndefExpr();
    } else {
      valExpr = new VarExpr(value);
    }
  } else if (Constant* constant = dyn_cast<Constant>(value)) {
    if (ConstantExpr* constantExpr = dyn_cast<ConstantExpr>(constant)) {
      if (constantExpr->getOpcode() == Instruction::GetElementPtr) {
        Value* ptrVal = constantExpr->getOperand(0);
        Expr* ptr = visitValue(ptrVal);

        Type* type = ptrVal->getType();
        gep_type_iterator typeI = gep_type_begin(constantExpr);
        for (unsigned i = 1, e = constantExpr->getNumOperands(); i != e; ++i, ++typeI) {
          Constant* idx = constantExpr->getOperand(i);
          if (StructType* structType = dyn_cast<StructType>(*typeI)) {
            assert(idx->getType()->isIntegerTy() && idx->getType()->getPrimitiveSizeInBits() == 32 && "Illegal struct idx");
            unsigned fieldNo = cast<ConstantInt>(idx)->getZExtValue();

            // Get structure layout information...
            const StructLayout* layout = targetData->getStructLayout(structType);

            // Add in the offset, as calculated by the structure layout info...
            ConstExpr* offset = new ConstExpr(layout->getElementOffset(fieldNo));
            ConstExpr* size = new ConstExpr(1);
            PtrArithExpr* ptrArith = new PtrArithExpr(ptr, offset, size);
            ptr = ptrArith;

            // Update type to refer to current element
            type = structType->getElementType(fieldNo);
          } else {
            // Update type to refer to current element
            type = cast<SequentialType>(type)->getElementType();

            // Get the array index and the size of each array element
            Expr* offset;
            if (idx->hasName()) {
              offset = new VarExpr(idx);
            } else {
              offset = new ConstExpr(idx);
            }
            ConstExpr* size = new ConstExpr(targetData->getTypeStoreSize(type));
            PtrArithExpr* ptrArith = new PtrArithExpr(ptr, offset, size);
            ptr = ptrArith;
          }
        }
        valExpr = ptr;
      } else if (constantExpr->getOpcode() == Instruction::BitCast) {

        // TODO: currently this is a noop instruction
        Value* ptrVal = constantExpr->getOperand(0);
        valExpr = visitValue(ptrVal);
      } else if (constantExpr->getOpcode() == Instruction::IntToPtr) {
        valExpr = new UndefExpr();
      } else {
        assert(false && "Constant expression of this type not supported");
      }
    } else if (ConstantInt* constantInt = dyn_cast<ConstantInt>(constant)) {
      valExpr = new ConstExpr(constantInt);
    } else if (constant->isNullValue()) {
      valExpr = new ConstExpr((int64_t)0);
    } else if (isa<UndefValue>(constant)) {
      valExpr = new UndefExpr();
    } else {
      assert(false && "This type of constant not supported");
    }
  } else {
    assert(false && "Value of this type not supported");
  }

  assert(valExpr != NULL);
  return valExpr;
}

void SmackInstVisitor::setBlock(Block* blockP) {
  block = blockP;
}

void SmackInstVisitor::addSuccBlock(Block* succBlock) {
  block->addSuccBlock(succBlock);
  
  BasicBlock* succBasicBlock = succBlock->getBasicBlock();
  for (BasicBlock::iterator
      i = succBasicBlock->begin(), e = succBasicBlock->end(); i != e && isa<PHINode>(i); ++i) {
    PHINode* phiNode = cast<PHINode>(i);
    if (Value* incomingValue = phiNode->getIncomingValueForBlock(block->getBasicBlock())) {
      Expr* incomingExpr = visitValue(incomingValue);
      VarExpr* incomingVar = new VarExpr(phiNode);
      AssignStmt* assignStmt = new AssignStmt(phiNode, incomingVar, incomingExpr);
      block->addInstruction(assignStmt);
    }
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
    if (inst.getType()->isIntegerTy(1)) {
      DEBUG(errs() << "Adding bool var\n");
      block->getParentProcedure()->addBoolVariable(&inst);
    } else {
      DEBUG(errs() << "Adding var\n");
      block->getParentProcedure()->addVariable(&inst);
    }
  }
}

void SmackInstVisitor::visitAllocaInst(AllocaInst& ai) {
  processInstruction(ai);

  Type* allocType = ai.getAllocatedType();
  unsigned typeSize = targetData->getTypeStoreSize(allocType);
  ConstExpr* typeSizeExpr = new ConstExpr(typeSize);
  Expr* arraySizeExpr = visitValue(ai.getArraySize());
  AllocaStmt* stmt = new AllocaStmt(&ai, typeSizeExpr, arraySizeExpr);
  block->addInstruction(stmt);
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

void SmackInstVisitor::visitCallInst(CallInst& ci) {
  processInstruction(ci);
  Function* calledFunction = ci.getCalledFunction();
  assert(calledFunction != NULL && "Indirect function calls currently not supported");
  std::string funcName = strip(calledFunction->getName().str());

  if (funcName.find("llvm.dbg.") == 0) {
    // skipping over debug info function calls
    return;
  }

  if (funcName == Common::ASSERT) {
    assert(ci.getNumOperands() == 2 && "Assertions should have only one parameter");
    Expr* expr = visitValue(ci.getOperand(0));
    AssertStmt* stmt = new AssertStmt(&ci, expr);
    block->addInstruction(stmt);
  } else if (funcName == Common::ASSUME) {
    assert(ci.getNumOperands() == 2 && "Assumes should have only one parameter");
    Expr* expr = visitValue(ci.getOperand(0));
    AssumeStmt* stmt = new AssumeStmt(&ci, expr);
    block->addInstruction(stmt);
  } else if (funcName == "malloc") {
    assert(ci.getNumOperands() == 2 && "Call to malloc should have only one parameter");
    assert(ci.hasOneUse());

    Type* allocType = ci.getType();
    for (Value::use_iterator i = ci.use_begin(), e = ci.use_end(); i != e; ++i) {
      Instruction* inst = cast<Instruction>(*i);
      if (BitCastInst* bitCastInst = dyn_cast<BitCastInst>(inst)) {
        allocType = cast<PointerType>(bitCastInst->getDestTy())->getElementType();
      }
    }

    Expr* arraySizeExpr = visitValue(ci.getOperand(0));

    MallocStmt* stmt = new MallocStmt(&ci, arraySizeExpr);
    block->addInstruction(stmt);
  } else if (funcName == "free") {
    assert(ci.getNumOperands() == 2 && "Call to free should have only one parameter");
    Expr* freedPtrExpr = visitValue(ci.getOperand(0));
    FreeStmt* stmt = new FreeStmt(&ci, freedPtrExpr);
    block->addInstruction(stmt);
  } else {
    CallStmt* stmt = new CallStmt(&ci);

#ifdef USE_DSA
    CallSite callSite = CallSite::get(&ci);
    if (ci.getCalledFunction() != NULL) {
      Function* calledFunction = ci.getCalledFunction();
      module->addCalledProcedure(calledFunction->getNameStr());
      CalledFunction* calledFunc = stmt->addCalledFunction(calledFunction);

      if ((Common::memoryType == DSA_INDEXED || Common::memoryType == DSA_SPLIT) &&
          tdDataStructures->hasDSGraph(*calledFunction)) {
        generateMemoryPairings(callSite, calledFunction, calledFunc);
      }
    } else {
      for (vector<const Function*>::iterator i = callTargetFinder->begin(callSite),
          ei = callTargetFinder->end(callSite); i != ei; ++i) {
        const Function* calledFunction = *i;
        module->addCalledProcedure(calledFunction->getNameStr());
        if (ci.getCalledValue()->getType() == calledFunction->getType()) {
          CalledFunction* calledFunc = stmt->addCalledFunction(calledFunction);

          if ((Common::memoryType == DSA_INDEXED || Common::memoryType == DSA_SPLIT) &&
              tdDataStructures->hasDSGraph(*calledFunction)) {
            generateMemoryPairings(callSite, calledFunction, calledFunc);
          }
        }
      }
    }
#else
    stmt->addCalledFunction(calledFunction);
#endif

    if (ci.getType()->getTypeID() != Type::VoidTyID) {
      VarExpr* returnVar = new VarExpr(&ci);
      stmt->setReturnVar(returnVar);
    }

    for (unsigned i = 0, e = ci.getNumOperands() - 1; i < e; ++i) {
      Expr* param = visitValue(ci.getOperand(i));
      stmt->addParam(param);
    }

    block->addInstruction(stmt);
  }
}

void SmackInstVisitor::visitReturnInst(ReturnInst& ri) {
  processInstruction(ri);

  ReturnStmt* stmt;
  Value* retVal = ri.getReturnValue();
  if (retVal == NULL) {
    // void return value
    stmt = new ReturnStmt(&ri);
  } else {
    Expr* retExpr = visitValue(retVal);
    stmt = new ReturnStmt(&ri, block->getParentProcedure()->getReturnVar(), retExpr);
  }
  block->addInstruction(stmt);
}

void SmackInstVisitor::visitLoadInst(LoadInst& li) {
  processInstruction(li);

  Value* ptr = li.getPointerOperand();
  MemExpr* memExpr = new MemExpr(visitValue(ptr), Memory::create());
  Expr* expr = new VarExpr(&li);
  AssignStmt* assignStmt = new AssignStmt(&li, expr, memExpr);
  block->addInstruction(assignStmt);
}

void SmackInstVisitor::visitStoreInst(StoreInst& si) {
  processInstruction(si);

  Value* ptr = si.getPointerOperand();
  MemExpr* memExpr = new MemExpr(visitValue(ptr), Memory::create());
  Expr* expr = visitValue(si.getOperand(0));
  AssignStmt* assignStmt = new AssignStmt(&si, memExpr, expr);
  block->addInstruction(assignStmt);
}

void SmackInstVisitor::visitGetElementPtrInst(GetElementPtrInst& gepi) {
  processInstruction(gepi);

  Value* ptrVal = gepi.getPointerOperand();
  Expr* ptr = visitValue(ptrVal);

  gep_type_iterator typeI = gep_type_begin(gepi);
  for (GetElementPtrInst::op_iterator
      idxI = gepi.idx_begin(), e = gepi.idx_end(); idxI != e; ++idxI, ++typeI) {
    if (StructType* structType = dyn_cast<StructType>(*typeI)) {
      assert((*idxI)->getType()->isIntegerTy() && (*idxI)->getType()->getPrimitiveSizeInBits() == 32 && "Illegal struct idx");
      unsigned fieldNo = cast<ConstantInt>(*idxI)->getZExtValue();

      // Get structure layout information...
      const StructLayout* layout = targetData->getStructLayout(structType);

      // Add in the offset, as calculated by the structure layout info...
      ConstExpr* offset = new ConstExpr(layout->getElementOffset(fieldNo));
      ConstExpr* size = new ConstExpr(1);
      PtrArithExpr* ptrArith = new PtrArithExpr(ptr, offset, size);
      ptr = ptrArith;
    } else {
      // Type refers to sequence element type
      Type* type = cast<SequentialType>(*typeI)->getElementType();

      // Get the array index and the size of each array element
      Expr* offset = visitValue(*idxI);
      ConstExpr* size = new ConstExpr(targetData->getTypeStoreSize(type));
      PtrArithExpr* ptrArith = new PtrArithExpr(ptr, offset, size);
      ptr = ptrArith;
    }
  }

  VarExpr* varExpr = new VarExpr(&gepi);
  AssignStmt* stmt = new AssignStmt(&gepi, varExpr, ptr);
  block->addInstruction(stmt);
}

void SmackInstVisitor::visitICmpInst(ICmpInst& ci) {
  processInstruction(ci);

  Expr* left = visitValue(ci.getOperand(0));
  Expr* right = visitValue(ci.getOperand(1));
  CmpStmt* cmpStmt = new CmpStmt(&ci, left, right);
  block->addInstruction(cmpStmt);
}

void SmackInstVisitor::visitZExtInst(ZExtInst& ci) {
  processInstruction(ci);

  Statement* stmt;
  if (ci.getSrcTy()->isIntegerTy() && ci.getSrcTy()->getPrimitiveSizeInBits() == 1) {
    stmt = new BoolToIntStmt(&ci, visitValue(ci.getOperand(0)));
  } else {
    stmt = new AssignStmt(&ci, new VarExpr(&ci), visitValue(ci.getOperand(0)));
  }
  block->addInstruction(stmt);
}

void SmackInstVisitor::visitSExtInst(SExtInst& ci) {
  processInstruction(ci);

  Statement* stmt;
  if (ci.getSrcTy()->isIntegerTy() && ci.getSrcTy()->getPrimitiveSizeInBits() == 1) {
    stmt = new BoolToIntStmt(&ci, visitValue(ci.getOperand(0)));
  } else {
    stmt = new AssignStmt(&ci, new VarExpr(&ci), visitValue(ci.getOperand(0)));
  }
  block->addInstruction(stmt);
}

void SmackInstVisitor::visitBitCastInst(BitCastInst& ci) {

  // TODO: currently this is a noop instruction
  processInstruction(ci);

  AssignStmt* assignStmt = new AssignStmt(&ci, new VarExpr(&ci), visitValue(ci.getOperand(0)));
  block->addInstruction(assignStmt);
}

void SmackInstVisitor::visitBinaryOperator(BinaryOperator& bo) {
  processInstruction(bo);

  Expr* left = visitValue(bo.getOperand(0));
  Expr* right = visitValue(bo.getOperand(1));
  BinaryOperatorStmt* binaryOperatorStmt = new BinaryOperatorStmt(&bo, left, right);
  block->addInstruction(binaryOperatorStmt);
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
