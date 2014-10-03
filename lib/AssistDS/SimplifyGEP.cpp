//===--------------- SimplifyGEP.cpp - Simplify GEPs types  ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Simplify GEPs with bitcasts (mostly cloned from InstCombine)
//
//===----------------------------------------------------------------------===//


#define DEBUG_TYPE "simplify-gep"

#include "assistDS/SimplifyGEP.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Operator.h"

#include <vector>

using namespace llvm;

//
// Method: preprocess()
//
// Description:
//  %p = bitcast %p1 to T1
//  gep(%p) ...
// ->
//  gep (bitcast %p1 to T1), ...
//
// Inputs:
//  M - A reference to the LLVM module to process
//
// Outputs:
//  M - The transformed LLVM module.
//
static void preprocess(Module& M) {
  for (Module::iterator F = M.begin(); F != M.end(); ++F){
    for (Function::iterator B = F->begin(), FE = F->end(); B != FE; ++B) {      
      for (BasicBlock::iterator I = B->begin(), BE = B->end(); I != BE; I++) {
        if(!(isa<GetElementPtrInst>(I)))
          continue;
        GetElementPtrInst *GEP = cast<GetElementPtrInst>(I);
        if(BitCastInst *BI = dyn_cast<BitCastInst>(GEP->getOperand(0))) {
          if(Constant *C = dyn_cast<Constant>(BI->getOperand(0))) {
            GEP->setOperand(0, ConstantExpr::getBitCast(C, BI->getType()));
          }
        }
      }
    }
  }
}
//
// Method: runOnModule()
//
// Description:
//  Entry point for this LLVM pass.
//  Find all GEPs, and simplify them.
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
bool SimplifyGEP::runOnModule(Module& M) {
  TD = &getAnalysis<DataLayoutPass>().getDataLayout();
  preprocess(M);
  for (Module::iterator F = M.begin(); F != M.end(); ++F){
    for (Function::iterator B = F->begin(), FE = F->end(); B != FE; ++B) {      
      for (BasicBlock::iterator I = B->begin(), BE = B->end(); I != BE; I++) {
        if(!(isa<GetElementPtrInst>(I)))
          continue;
        GetElementPtrInst *GEP = cast<GetElementPtrInst>(I);
        Value *PtrOp = GEP->getOperand(0);
        Value *StrippedPtr = PtrOp->stripPointerCasts();
        // Check if the GEP base pointer is enclosed in a cast
        if (StrippedPtr != PtrOp) {
          const PointerType *StrippedPtrTy =cast<PointerType>(StrippedPtr->getType());
          bool HasZeroPointerIndex = false;
          if (ConstantInt *C = dyn_cast<ConstantInt>(GEP->getOperand(1)))
            HasZeroPointerIndex = C->isZero();
          // Transform: GEP (bitcast [10 x i8]* X to [0 x i8]*), i32 0, ...
          // into     : GEP [10 x i8]* X, i32 0, ...
          //
          // Likewise, transform: GEP (bitcast i8* X to [0 x i8]*), i32 0, ...
          //           into     : GEP i8* X, ...
          // 
          // This occurs when the program declares an array extern like "int X[];"
          if (HasZeroPointerIndex) {
            const PointerType *CPTy = cast<PointerType>(PtrOp->getType());
            if (const ArrayType *CATy =
                dyn_cast<ArrayType>(CPTy->getElementType())) {
              // GEP (bitcast i8* X to [0 x i8]*), i32 0, ... ?
              if (CATy->getElementType() == StrippedPtrTy->getElementType()) {
                // -> GEP i8* X, ...
                SmallVector<Value*, 8> Idx(GEP->idx_begin()+1, GEP->idx_end());
                GetElementPtrInst *Res =
                  GetElementPtrInst::Create(StrippedPtr, Idx, GEP->getName(), GEP);
                Res->setIsInBounds(GEP->isInBounds());
                GEP->replaceAllUsesWith(Res);
                continue;
              }

              if (const ArrayType *XATy =
                  dyn_cast<ArrayType>(StrippedPtrTy->getElementType())){
                // GEP (bitcast [10 x i8]* X to [0 x i8]*), i32 0, ... ?
                if (CATy->getElementType() == XATy->getElementType()) {
                  // -> GEP [10 x i8]* X, i32 0, ...
                  // At this point, we know that the cast source type is a pointer
                  // to an array of the same type as the destination pointer
                  // array.  Because the array type is never stepped over (there
                  // is a leading zero) we can fold the cast into this GEP.
                  GEP->setOperand(0, StrippedPtr);
                  continue;
                }
              }
            }   
          } else if (GEP->getNumOperands() == 2) {
            // Transform things like:
            // %t = getelementptr i32* bitcast ([2 x i32]* %str to i32*), i32 %V
            // into:  %t1 = getelementptr [2 x i32]* %str, i32 0, i32 %V; bitcast
            Type *SrcElTy = StrippedPtrTy->getElementType();
            Type *ResElTy=cast<PointerType>(PtrOp->getType())->getElementType();
            if (TD && SrcElTy->isArrayTy() &&
                TD->getTypeAllocSize(cast<ArrayType>(SrcElTy)->getElementType()) ==
                TD->getTypeAllocSize(ResElTy)) {
              Value *Idx[2];
              Idx[0] = Constant::getNullValue(Type::getInt32Ty(GEP->getContext()));
              Idx[1] = GEP->getOperand(1);
              Value *NewGEP = GetElementPtrInst::Create(StrippedPtr, Idx,
                                                        GEP->getName(), GEP);
              // V and GEP are both pointer types --> BitCast
              GEP->replaceAllUsesWith(new BitCastInst(NewGEP, GEP->getType(), GEP->getName(), GEP));
              continue;
            }

            // Transform things like:
            // getelementptr i8* bitcast ([100 x double]* X to i8*), i32 %tmp
            //   (where tmp = 8*tmp2) into:
            // getelementptr [100 x double]* %arr, i32 0, i32 %tmp2; bitcast

            if (TD && SrcElTy->isArrayTy() && ResElTy->isIntegerTy(8)) {
              uint64_t ArrayEltSize =
                TD->getTypeAllocSize(cast<ArrayType>(SrcElTy)->getElementType());

              // Check to see if "tmp" is a scale by a multiple of ArrayEltSize.  We
              // allow either a mul, shift, or constant here.
              Value *NewIdx = 0;
              ConstantInt *Scale = 0;
              if (ArrayEltSize == 1) {
                NewIdx = GEP->getOperand(1);
                Scale = ConstantInt::get(cast<IntegerType>(NewIdx->getType()), 1);
              } else if (ConstantInt *CI = dyn_cast<ConstantInt>(GEP->getOperand(1))) {
                NewIdx = ConstantInt::get(CI->getType(), 1);
                Scale = CI;
              } else if (Instruction *Inst =dyn_cast<Instruction>(GEP->getOperand(1))){
                if (Inst->getOpcode() == Instruction::Shl &&
                    isa<ConstantInt>(Inst->getOperand(1))) {
                  ConstantInt *ShAmt = cast<ConstantInt>(Inst->getOperand(1));
                  uint32_t ShAmtVal = ShAmt->getLimitedValue(64);
                  Scale = ConstantInt::get(cast<IntegerType>(Inst->getType()),
                                           1ULL << ShAmtVal);
                  NewIdx = Inst->getOperand(0);
                } else if (Inst->getOpcode() == Instruction::Mul &&
                           isa<ConstantInt>(Inst->getOperand(1))) {
                  Scale = cast<ConstantInt>(Inst->getOperand(1));
                  NewIdx = Inst->getOperand(0);
                }
              }

              // If the index will be to exactly the right offset with the scale taken
              // out, perform the transformation. Note, we don't know whether Scale is
              // signed or not. We'll use unsigned version of division/modulo
              // operation after making sure Scale doesn't have the sign bit set.
              if (ArrayEltSize && Scale && Scale->getSExtValue() >= 0LL &&
                  Scale->getZExtValue() % ArrayEltSize == 0) {
                Scale = ConstantInt::get(Scale->getType(),
                                         Scale->getZExtValue() / ArrayEltSize);
                if (Scale->getZExtValue() != 1) {
                  Constant *C = ConstantExpr::getIntegerCast(Scale, NewIdx->getType(),
                                                             false /*ZExt*/);
                  NewIdx = BinaryOperator::Create(BinaryOperator::Mul, NewIdx, C, "idxscale");
                }

                // Insert the new GEP instruction.
                Value *Idx[2];
                Idx[0] = Constant::getNullValue(Type::getInt32Ty(GEP->getContext()));
                Idx[1] = NewIdx;
                Value *NewGEP = GetElementPtrInst::Create(StrippedPtr, Idx,
                                                          GEP->getName(), GEP);
                GEP->replaceAllUsesWith(new BitCastInst(NewGEP, GEP->getType(), GEP->getName(), GEP));
                continue;
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
char SimplifyGEP::ID = 0;

// Register the pass
static RegisterPass<SimplifyGEP>
X("simplify-gep", "Simplify GEPs");
