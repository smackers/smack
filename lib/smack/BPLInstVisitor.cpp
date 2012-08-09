//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "BPLInstVisitor.h"
      
using namespace smack;

Expr* BPLInstVisitor::visitValue(Value* value) {
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

void BPLInstVisitor::setBPLBlock(BPLBlock* blockP) {
  block = blockP;
}

void BPLInstVisitor::addSuccBlock(BPLBlock* succBlock) {
  block->addSuccBlock(succBlock);
  
  BasicBlock* succBasicBlock = succBlock->getBasicBlock();
  for (BasicBlock::iterator
      i = succBasicBlock->begin(), e = succBasicBlock->end(); i != e && isa<PHINode>(i); ++i) {
    PHINode* phiNode = cast<PHINode>(i);
    if (Value* incomingValue = phiNode->getIncomingValueForBlock(block->getBasicBlock())) {
      Expr* incomingExpr = visitValue(incomingValue);
      VarExpr* incomingVar = new VarExpr(phiNode);
      BPLAssignInst* assignInst = new BPLAssignInst(phiNode, incomingVar, incomingExpr);
      block->addInstruction(assignInst);
    }
  }
}

void BPLInstVisitor::visitInstruction(Instruction& inst) {
  DEBUG(errs() << "Instruction not handled: " << inst << "\n");
  assert(false && "Instruction not handled");
}

void BPLInstVisitor::processInstruction(Instruction& inst) {
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

void BPLInstVisitor::visitAllocaInst(AllocaInst& ai) {
  processInstruction(ai);

  Type* allocType = ai.getAllocatedType();
  unsigned typeSize = targetData->getTypeStoreSize(allocType);
  ConstExpr* typeSizeExpr = new ConstExpr(typeSize);
  Expr* arraySizeExpr = visitValue(ai.getArraySize());
  BPLAllocaInst* bplInst = new BPLAllocaInst(&ai, typeSizeExpr, arraySizeExpr);
  block->addInstruction(bplInst);
}

void BPLInstVisitor::visitBranchInst(BranchInst& bi) {
  processInstruction(bi);
}

void BPLInstVisitor::visitPHINode(PHINode& phi) {
  processInstruction(phi);
}

void BPLInstVisitor::visitCallInst(CallInst& ci) {
  processInstruction(ci);

  if (ci.getCalledFunction() != NULL && ci.getCalledFunction()->getName() == Common::ASSERT) {
    assert(ci.getNumOperands() == 2 && "Assertions should have only one parameter");
    Expr* expr = visitValue(ci.getOperand(0));
    BPLAssertInst* bplInst = new BPLAssertInst(&ci, expr);
    block->addInstruction(bplInst);
  } else if (ci.getCalledFunction() != NULL && ci.getCalledFunction()->getName() == Common::ASSUME) {
    assert(ci.getNumOperands() == 2 && "Assumes should have only one parameter");
    Expr* expr = visitValue(ci.getOperand(0));
    BPLAssumeInst* bplInst = new BPLAssumeInst(&ci, expr);
    block->addInstruction(bplInst);
  } else if (ci.getCalledFunction() != NULL && ci.getCalledFunction()->getName() == "malloc") {
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

    BPLMallocInst* bplInst = new BPLMallocInst(&ci, arraySizeExpr);
    block->addInstruction(bplInst);
  } else if (ci.getCalledFunction() != NULL && ci.getCalledFunction()->getName() == "free") {
    assert(ci.getNumOperands() == 2 && "Call to free should have only one parameter");
    Expr* freedPtrExpr = visitValue(ci.getOperand(0));
    BPLFreeInst* bplInst = new BPLFreeInst(&ci, freedPtrExpr);
    block->addInstruction(bplInst);
  } else {
    BPLCallInst* bplCallInst = new BPLCallInst(&ci);

#ifdef USE_DSA
    CallSite callSite = CallSite::get(&ci);
    if (ci.getCalledFunction() != NULL) {
      Function* calledFunction = ci.getCalledFunction();
      bplModule->addCalledProcedure(calledFunction->getNameStr());
      CalledFunction* calledFunc = bplCallInst->addCalledFunction(calledFunction);

      if ((Common::memoryType == DSA_INDEXED || Common::memoryType == DSA_SPLIT) &&
          tdDataStructures->hasDSGraph(*calledFunction)) {
        generateMemoryPairings(callSite, calledFunction, calledFunc);
      }
    } else {
      for (std::vector<const Function*>::iterator i = callTargetFinder->begin(callSite),
          ei = callTargetFinder->end(callSite); i != ei; ++i) {
        const Function* calledFunction = *i;
        bplModule->addCalledProcedure(calledFunction->getNameStr());
        if (ci.getCalledValue()->getType() == calledFunction->getType()) {
          CalledFunction* calledFunc = bplCallInst->addCalledFunction(calledFunction);

          if ((Common::memoryType == DSA_INDEXED || Common::memoryType == DSA_SPLIT) &&
              tdDataStructures->hasDSGraph(*calledFunction)) {
            generateMemoryPairings(callSite, calledFunction, calledFunc);
          }
        }
      }
    }
#else
    Function* calledFunction = ci.getCalledFunction();
    assert(calledFunction != NULL && "Indirect function calls currently not supported");
    bplCallInst->addCalledFunction(calledFunction);
#endif

    if (ci.getType()->getTypeID() != Type::VoidTyID) {
      VarExpr* returnVar = new VarExpr(&ci);
      bplCallInst->setReturnVar(returnVar);
    }

    for (unsigned i = 0, e = ci.getNumOperands() - 1; i < e; ++i) {
      Expr* param = visitValue(ci.getOperand(i));
      bplCallInst->addParam(param);
    }

    block->addInstruction(bplCallInst);
  }
}

void BPLInstVisitor::visitReturnInst(ReturnInst& ri) {
  processInstruction(ri);

  BPLReturnInst* bplInst;
  Value* retVal = ri.getReturnValue();
  if (retVal == NULL) {
    // void return value
    bplInst = new BPLReturnInst(&ri);
  } else {
    Expr* retExpr = visitValue(retVal);
    bplInst = new BPLReturnInst(&ri, block->getParentProcedure()->getReturnVar(), retExpr);
  }
  block->addInstruction(bplInst);
}

void BPLInstVisitor::visitLoadInst(LoadInst& li) {
  processInstruction(li);

  Value* ptr = li.getPointerOperand();
  MemExpr* memExpr = new MemExpr(visitValue(ptr), Memory::create());
  Expr* expr = new VarExpr(&li);
  BPLAssignInst* assignInst = new BPLAssignInst(&li, expr, memExpr);
  block->addInstruction(assignInst);
}

void BPLInstVisitor::visitStoreInst(StoreInst& si) {
  processInstruction(si);

  Value* ptr = si.getPointerOperand();
  MemExpr* memExpr = new MemExpr(visitValue(ptr), Memory::create());
  Expr* expr = visitValue(si.getOperand(0));
  BPLAssignInst* assignInst = new BPLAssignInst(&si, memExpr, expr);
  block->addInstruction(assignInst);
}

void BPLInstVisitor::visitGetElementPtrInst(GetElementPtrInst& gepi) {
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
  BPLAssignInst* bplInst = new BPLAssignInst(&gepi, varExpr, ptr);
  block->addInstruction(bplInst);
}

void BPLInstVisitor::visitICmpInst(ICmpInst& ci) {
  processInstruction(ci);

  Expr* left = visitValue(ci.getOperand(0));
  Expr* right = visitValue(ci.getOperand(1));
  BPLCmpInst* cmpInst = new BPLCmpInst(&ci, left, right);
  block->addInstruction(cmpInst);
}

void BPLInstVisitor::visitZExtInst(ZExtInst& ci) {
  processInstruction(ci);

  BPLInstruction* bplInst;
  if (ci.getSrcTy()->isIntegerTy() && ci.getSrcTy()->getPrimitiveSizeInBits() == 1) {
    bplInst = new BPLBoolToIntInst(&ci, visitValue(ci.getOperand(0)));
  } else {
    bplInst = new BPLAssignInst(&ci, new VarExpr(&ci), visitValue(ci.getOperand(0)));
  }
  block->addInstruction(bplInst);
}

void BPLInstVisitor::visitSExtInst(SExtInst& ci) {
  processInstruction(ci);

  BPLInstruction* bplInst;
  if (ci.getSrcTy()->isIntegerTy() && ci.getSrcTy()->getPrimitiveSizeInBits() == 1) {
    bplInst = new BPLBoolToIntInst(&ci, visitValue(ci.getOperand(0)));
  } else {
    bplInst = new BPLAssignInst(&ci, new VarExpr(&ci), visitValue(ci.getOperand(0)));
  }
  block->addInstruction(bplInst);
}

void BPLInstVisitor::visitBitCastInst(BitCastInst& ci) {

  // TODO: currently this is a noop instruction
  processInstruction(ci);

  BPLAssignInst* assignInst = new BPLAssignInst(&ci, new VarExpr(&ci), visitValue(ci.getOperand(0)));
  block->addInstruction(assignInst);
}

void BPLInstVisitor::visitBinaryOperator(BinaryOperator& bo) {
  processInstruction(bo);

  Expr* left = visitValue(bo.getOperand(0));
  Expr* right = visitValue(bo.getOperand(1));
  BPLBinaryOperatorInst* binaryOperatorInst = new BPLBinaryOperatorInst(&bo, left, right);
  block->addInstruction(binaryOperatorInst);
}
