//===- CostModel.cpp ------ Cost Model Analysis ---------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file defines the cost model analysis. It provides a very basic cost
// estimation for LLVM-IR. This analysis uses the services of the codegen
// to approximate the cost of any IR instruction when lowered to machine
// instructions. The cost results are unit-less and the cost number represents
// the throughput of the machine assuming that all loads hit the cache, all
// branches are predicted, etc. The cost numbers can be added in order to
// compare two or more transformation alternatives.
//
//===----------------------------------------------------------------------===//
#include "smack/AddTiming.h"

#include "llvm/ADT/STLExtras.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Value.h"
#include "llvm/Pass.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"

#include <sstream>

using namespace llvm;

#define CM_NAME "cost-model"
#define DEBUG_TYPE CM_NAME

namespace smack {

// Register this pass.
char AddTiming::ID = 0;
static RegisterPass<AddTiming>
X("add-timing-info", "Add Timing Info");


void
AddTiming::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequired<TargetTransformInfoWrapperPass>();
}

bool
AddTiming::runOnFunction(Function &F) {
 this->F = &F;
 TTI = &(getAnalysis<TargetTransformInfoWrapperPass>().getTTI(F));

  for (Function::iterator B = F.begin(), BE = F.end(); B != BE; ++B) {
    for (BasicBlock::iterator it = B->begin(), e = B->end(); it != e; ++it) {
      Instruction *Inst = &*it;
      unsigned Cost = getInstructionCost(Inst);
      if (Cost != (unsigned)NO_TIMING_INFO) {
	addTimingMetadata(Inst, "smack.InstTimingCost.Int64", Cost);
	addTimingMetadata(Inst, "smack.LLVMInstructionName", Naming::nameLLVMInstruction(Inst));
      } 
    }
  }
 
 return false;
}


static TargetTransformInfo::OperandValueKind getOperandInfo(Value *V) {
  TargetTransformInfo::OperandValueKind OpInfo =
    TargetTransformInfo::OK_AnyValue;

  // Check for a splat of a constant or for a non uniform vector of constants.
  if (isa<ConstantVector>(V) || isa<ConstantDataVector>(V)) {
    OpInfo = TargetTransformInfo::OK_NonUniformConstantValue;
    if (cast<Constant>(V)->getSplatValue() != nullptr)
      OpInfo = TargetTransformInfo::OK_UniformConstantValue;
  }

  return OpInfo;
}

unsigned AddTiming::getInstructionCost(const Instruction *I) const {
  if (!TTI)
    return NO_TIMING_INFO;

  switch (I->getOpcode()) {
  case Instruction::GetElementPtr:{
    Type *ValTy = I->getOperand(0)->getType()->getPointerElementType();
    return TTI->getAddressComputationCost(ValTy);
  }

  case Instruction::Ret:
  case Instruction::PHI:
  case Instruction::Br: {
    return TTI->getCFInstrCost(I->getOpcode());
  }
  case Instruction::Add:
  case Instruction::FAdd:
  case Instruction::Sub:
  case Instruction::FSub:
  case Instruction::Mul:
  case Instruction::FMul:
  case Instruction::UDiv:
  case Instruction::SDiv:
  case Instruction::FDiv:
  case Instruction::URem:
  case Instruction::SRem:
  case Instruction::FRem:
  case Instruction::Shl:
  case Instruction::LShr:
  case Instruction::AShr:
  case Instruction::And:
  case Instruction::Or:
  case Instruction::Xor: {
    TargetTransformInfo::OperandValueKind Op1VK =
      getOperandInfo(I->getOperand(0));
    TargetTransformInfo::OperandValueKind Op2VK =
      getOperandInfo(I->getOperand(1));
    return TTI->getArithmeticInstrCost(I->getOpcode(), I->getType(), Op1VK,
                                       Op2VK);
  }
  case Instruction::Select: {
    const SelectInst *SI = cast<SelectInst>(I);
    Type *CondTy = SI->getCondition()->getType();
    return TTI->getCmpSelInstrCost(I->getOpcode(), I->getType(), CondTy);
  }
  case Instruction::ICmp:
  case Instruction::FCmp: {
    Type *ValTy = I->getOperand(0)->getType();
    return TTI->getCmpSelInstrCost(I->getOpcode(), ValTy);
  }
  case Instruction::Store: {
    const StoreInst *SI = cast<StoreInst>(I);
    Type *ValTy = SI->getValueOperand()->getType();
    return TTI->getMemoryOpCost(I->getOpcode(), ValTy,
                                 SI->getAlignment(),
                                 SI->getPointerAddressSpace());
  }
  case Instruction::Load: {
    const LoadInst *LI = cast<LoadInst>(I);
    return TTI->getMemoryOpCost(I->getOpcode(), I->getType(),
                                 LI->getAlignment(),
                                 LI->getPointerAddressSpace());
  }
  case Instruction::ZExt:
  case Instruction::SExt:
  case Instruction::FPToUI:
  case Instruction::FPToSI:
  case Instruction::FPExt:
  case Instruction::PtrToInt:
  case Instruction::IntToPtr:
  case Instruction::SIToFP:
  case Instruction::UIToFP:
  case Instruction::Trunc:
  case Instruction::FPTrunc:
  case Instruction::BitCast:
  case Instruction::AddrSpaceCast: {
    Type *SrcTy = I->getOperand(0)->getType();
    return TTI->getCastInstrCost(I->getOpcode(), I->getType(), SrcTy);
  }
  case Instruction::ExtractElement: {
    return NO_TIMING_INFO;
  }
  case Instruction::InsertElement: {
    return NO_TIMING_INFO;
  }
  case Instruction::ShuffleVector: {
    return NO_TIMING_INFO;
  }
  case Instruction::Call: {
    if (const IntrinsicInst *II = dyn_cast<IntrinsicInst>(I)) {
      SmallVector<Type*, 4> Tys;
      for (unsigned J = 0, JE = II->getNumArgOperands(); J != JE; ++J)
        Tys.push_back(II->getArgOperand(J)->getType());

      return TTI->getIntrinsicInstrCost(II->getIntrinsicID(), II->getType(),
                                        Tys);
    }
    
    return NO_TIMING_INFO;
  }
  default:
    // We don't have any information on this instruction.
    return NO_TIMING_INFO;
  }
}
  
void AddTiming::addTimingMetadata(Instruction *Inst, const std::string &name, const std::string& value) const {
  LLVMContext& C = Inst->getContext();
  MDNode* N = MDNode::get(C, MDString::get(C, value));
  Inst->setMetadata(name, N);
}

  
void AddTiming::addTimingMetadata(Instruction *Inst, const std::string &name, unsigned cost) const {
  LLVMContext& C = Inst->getContext();
  MDNode* N = MDNode::get(C, ConstantAsMetadata::get(ConstantInt::get(C, llvm::APInt(64, cost, false))));
  Inst->setMetadata(name, N);
}
  
void AddTiming::print(raw_ostream &OS, const Module*) const {
  if (!F)
    return;

  for (Function::iterator B = F->begin(), BE = F->end(); B != BE; ++B) {
    for (BasicBlock::iterator it = B->begin(), e = B->end(); it != e; ++it) {
      Instruction *Inst = &*it;
      unsigned Cost = getInstructionCost(Inst);
      if (Cost != (unsigned)NO_TIMING_INFO) {
        OS << "Cost Model: Found an estimated cost of " << Cost;
      } else {
        OS << "Cost Model: Unknown cost";
      }
      OS << " for instruction: "<< *Inst << "\n";
    }
  }
}
}//namespace smack
