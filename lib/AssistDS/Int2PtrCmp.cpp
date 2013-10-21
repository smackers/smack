//===-- Int2PtrCmp.cpp - Merge inttoptr/ptrtoint --------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Remove unnecessary inttoptr casts
// Specially ones used in just compares
// Most cases derived from InstCombine
//
//===----------------------------------------------------------------------===//
#define DEBUG_TYPE "int2ptr-cmp"

#include "assistDS/Int2PtrCmp.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/PatternMatch.h"

#include <set>
#include <map>
#include <vector>

using namespace llvm;
using namespace PatternMatch;

//
// Method: runOnModule()
//
// Description:
//  Entry point for this LLVM pass.
//  Remove unnecessary inttoptr instructions.
//
// Inputs:
//  M - A reference to the LLVM module to transform
//
// Outputs:
//  M - The transformed LLVM module.
//
// Return value:
//  true  - The module was modified.
//  false - The module was not modified.
//
bool Int2PtrCmp::runOnModule(Module& M) {
  TD = &getAnalysis<DataLayout>();
  for (Module::iterator F = M.begin(); F != M.end(); ++F) {
    for (Function::iterator B = F->begin(), FE = F->end(); B != FE; ++B) {      
      for (BasicBlock::iterator I = B->begin(), BE = B->end(); I != BE;) {
        // ptrtoint(inttoptr ty Y) to ty -> Y 
        if(PtrToIntInst *P2I = dyn_cast<PtrToIntInst>(I++)) {
          if(IntToPtrInst *I2P = dyn_cast<IntToPtrInst>(P2I->getOperand(0))) {
            if(I2P->getSrcTy() == P2I->getDestTy()){
              P2I->replaceAllUsesWith(I2P->getOperand(0));
              P2I->eraseFromParent();
              if(I2P->use_empty()) {
                // If this is the only use of the cast delete it.
                I2P->eraseFromParent();
              }
            }
          }
        }
      }
      for (BasicBlock::iterator I = B->begin(), BE = B->end(); I != BE;) {
        //icmp pred inttoptr(X), null  -> icmp pred X 0
        if(ICmpInst *CI = dyn_cast<ICmpInst>(I++)) {
          Value *Op0 = CI->getOperand(0);
          Value *Op1 = CI->getOperand(1);
          if (Constant *RHSC = dyn_cast<Constant>(Op1)) {
            if (Instruction *LHSI = dyn_cast<Instruction>(Op0)){
              if(LHSI->getOpcode() == Instruction::IntToPtr) {
                if (RHSC->isNullValue() && TD &&
                    TD->getIntPtrType(RHSC->getContext(), 0) ==
                    LHSI->getOperand(0)->getType()){
                  ICmpInst *CI_new = new ICmpInst(CI, CI->getPredicate(), LHSI->getOperand(0),
                                                  Constant::getNullValue(LHSI->getOperand(0)->getType()));

                  CI->replaceAllUsesWith(CI_new);
                  CI->eraseFromParent();
                  if(LHSI->use_empty()) {
                    // If this is the only use of the cast delete it.
                    LHSI->eraseFromParent();
                  }
                }
              }
            }
          }
        }
      }
    }
  }

  for (Module::iterator F = M.begin(); F != M.end(); ++F) {
    for (Function::iterator B = F->begin(), FE = F->end(); B != FE; ++B) {      
      for (BasicBlock::iterator I = B->begin(), BE = B->end(); I != BE;) {
        if(ICmpInst *ICI = dyn_cast<ICmpInst>(I++)) {
          Value *Op0 = ICI->getOperand(0);
          Value *Op1 = ICI->getOperand(1);
          if (ConstantInt *CI = dyn_cast<ConstantInt>(Op1)) {
            // Since the RHS is a ConstantInt (CI), if the left hand side is an
            // instruction, see if that instruction also has constants so that the
            // instruction can be folded into the icmp
            if (Instruction *LHSI = dyn_cast<Instruction>(Op0)){
              if(LHSI->getOpcode() == Instruction::Or) {
                if (!ICI->isEquality() || !CI->isNullValue() || !LHSI->hasOneUse())
                  break;
                Value *P, *Q, *R;
                if (match(LHSI, m_Or(m_PtrToInt(m_Value(P)), m_PtrToInt(m_Value(Q))))) {
                  // Simplify icmp eq (or (ptrtoint P), (ptrtoint Q)), 0
                  // -> and (icmp eq P, null), (icmp eq Q, null).
                  Value *ICIP = new ICmpInst(ICI, ICI->getPredicate(), P,
                                             Constant::getNullValue(P->getType()));
                  Value *ICIQ = new ICmpInst(ICI, ICI->getPredicate(), Q,
                                             Constant::getNullValue(Q->getType()));
                  Instruction *Op;
                  if (ICI->getPredicate() == ICmpInst::ICMP_EQ)
                    Op = BinaryOperator::CreateAnd(ICIP, ICIQ,"",ICI);
                  else
                    Op = BinaryOperator::CreateOr(ICIP, ICIQ, "", ICI);
                  ICI->replaceAllUsesWith(Op);

                } else if(match(LHSI, m_Or(m_Or(m_PtrToInt(m_Value(P)), 
                                                m_PtrToInt(m_Value(Q))), 
                                           m_PtrToInt(m_Value(R))))) {
                  // Simplify icmp eq (or (or (ptrtoint P), (ptrtoint Q)), ptrtoint(R)), 0
                  // -> and (and (icmp eq P, null), (icmp eq Q, null)), (icmp eq R, null).
                  Value *ICIP = new ICmpInst(ICI, ICI->getPredicate(), P,
                                             Constant::getNullValue(P->getType()));
                  Value *ICIQ = new ICmpInst(ICI, ICI->getPredicate(), Q,
                                             Constant::getNullValue(Q->getType()));
                  Value *ICIR = new ICmpInst(ICI, ICI->getPredicate(), R,
                                             Constant::getNullValue(R->getType()));
                  Instruction *Op;
                  if (ICI->getPredicate() == ICmpInst::ICMP_EQ)
                    Op = BinaryOperator::CreateAnd(ICIP, ICIQ,"",ICI);
                  else
                    Op = BinaryOperator::CreateOr(ICIP, ICIQ, "", ICI);

                  if (ICI->getPredicate() == ICmpInst::ICMP_EQ)
                    Op = BinaryOperator::CreateAnd(Op, ICIR,"",ICI);
                  else
                    Op = BinaryOperator::CreateOr(Op, ICIR, "", ICI);
                  ICI->replaceAllUsesWith(Op);

                } else if(match(LHSI, m_Or(m_PtrToInt(m_Value(Q)), m_Or(
                        m_PtrToInt(m_Value(P)), m_PtrToInt(m_Value(R)))))) {
                  // Simplify icmp eq (or  (ptrtoint P), or((ptrtoint Q), ptrtoint(R))), 0
                  // -> and (icmp eq P, null), (and (icmp eq Q, null), (icmp eq R, null)).
                  Value *ICIP = new ICmpInst(ICI, ICI->getPredicate(), P,
                                             Constant::getNullValue(P->getType()));
                  Value *ICIQ = new ICmpInst(ICI, ICI->getPredicate(), Q,
                                             Constant::getNullValue(Q->getType()));
                  Value *ICIR = new ICmpInst(ICI, ICI->getPredicate(), R,
                                             Constant::getNullValue(R->getType()));
                  Instruction *Op;
                  if (ICI->getPredicate() == ICmpInst::ICMP_EQ)
                    Op = BinaryOperator::CreateAnd(ICIP, ICIQ,"",ICI);
                  else
                    Op = BinaryOperator::CreateOr(ICIP, ICIQ, "", ICI);

                  if (ICI->getPredicate() == ICmpInst::ICMP_EQ)
                    Op = BinaryOperator::CreateAnd(Op, ICIR,"",ICI);
                  else
                    Op = BinaryOperator::CreateOr(Op, ICIR, "", ICI);
                  ICI->replaceAllUsesWith(Op);
                }
              }
            }
          }
        }
      }
    }
  }
  return true;
}

// Pass ID variable
char Int2PtrCmp::ID = 0;

// Register the pass
static RegisterPass<Int2PtrCmp>
X("int2ptrcmp", "Simplify inttoptr/ptrtoint insts");
