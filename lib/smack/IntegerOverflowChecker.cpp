//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/IntegerOverflowChecker.h"
#include "smack/Naming.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Constants.h"
#include "smack/Debug.h"
#include "llvm/IR/ValueSymbolTable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/Regex.h"
#include <string>
#include "llvm/ADT/APInt.h"
#include "smack/SmackOptions.h"

namespace smack {

using namespace llvm;

Regex OVERFLOW_INTRINSICS("^llvm.(u|s)(add|sub|mul).with.overflow.i([0-9]+)$");

std::map<std::string, Instruction::BinaryOps> IntegerOverflowChecker::INSTRUCTION_TABLE {
  {"add", Instruction::Add},
  {"sub", Instruction::Sub},
  {"mul", Instruction::Mul}
};

std::string getMax(unsigned bits, bool is_signed) {
  if (is_signed) {
    return APInt::getSignedMaxValue(bits).toString(10, true);
  } else {
    return APInt::getMaxValue(bits).toString(10, false);
  }
}

std::string getMin(unsigned bits, bool is_signed) {
  if (is_signed) {
    return APInt::getSignedMinValue(bits).toString(10, true);
  } else {
    return APInt::getMinValue(bits).toString(10, false);
  }
}

bool IntegerOverflowChecker::runOnModule(Module& m) {
  Function* va = m.getFunction("__SMACK_overflow_false");
  assert(va != NULL && "Function __SMACK_overflow_false should be present.");
  Function* co = m.getFunction("__SMACK_check_overflow");
  assert(co != NULL && "Function __SMACK_check_overflow should be present.");
  Function* verif_assume = m.getFunction("__VERIFIER_assume");
  assert(verif_assume != NULL && "Function __VERIFIER_assume should be present.");
  std::vector<Instruction*> inst_to_remove;
  for (auto& F : m) {
    if (!Naming::isSmackName(F.getName())) {
      for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
        if (auto ci = dyn_cast<CallInst>(&*I)) {
          Function* f = ci->getCalledFunction();
          if (f && f->hasName() && f->getName() == "llvm.trap") {
            ci->setCalledFunction(va);
          }
        }
        if (auto ei = dyn_cast<ExtractValueInst>(&*I)) {
          if (auto ci = dyn_cast<CallInst>(ei->getAggregateOperand())) {
            Function* f = ci->getCalledFunction();
            SmallVectorImpl<StringRef> *ar = new SmallVector<StringRef, 3>;
            if (f && f->hasName() && OVERFLOW_INTRINSICS.match(f->getName().str(), ar)) {
              bool is_signed = ar->begin()[1].str() == "s";
              std::string op = ar->begin()[2].str();
              std::string len = ar->begin()[3].str();
              int bits = std::stoi(len);
              if (ei->getIndices()[0] == 1) {
                Instruction* prev = &*std::prev(I);
                Value* o1 = ci->getArgOperand(0);
                Value* o2 = ci->getArgOperand(1);
                CastInst* so1, *so2;
                if (is_signed) {
                  so1 = CastInst::CreateSExtOrBitCast(o1, IntegerType::get(F.getContext(), bits*2), "", &*I);
                  so2 = CastInst::CreateSExtOrBitCast(o2, IntegerType::get(F.getContext(), bits*2), "", &*I);
                } else {
                  so1 = CastInst::CreateZExtOrBitCast(o1, IntegerType::get(F.getContext(), bits*2), "", &*I);
                  so2 = CastInst::CreateZExtOrBitCast(o2, IntegerType::get(F.getContext(), bits*2), "", &*I);
                }

                BinaryOperator* ai = BinaryOperator::Create(INSTRUCTION_TABLE.at(op), so1, so2, "", &*I);
                if (prev && isa<ExtractValueInst>(prev)) {
                  ExtractValueInst* pei = cast<ExtractValueInst>(prev);
                  if (auto pci = dyn_cast<CallInst>(pei->getAggregateOperand())) {
                    if (pci == ci) {
                      CastInst* tr = CastInst::CreateTruncOrBitCast(ai, IntegerType::get(F.getContext(), bits), "", &*I);
                      prev->replaceAllUsesWith(tr);
                      inst_to_remove.push_back(prev);
                    }
                  }
                }

                BinaryOperator* flag;
                inst_to_remove.push_back(&*I);
                if (smack::SmackOptions::IntegerOverflow) {
                  ConstantInt* max = ConstantInt::get(IntegerType::get(F.getContext(), bits*2), getMax(bits, is_signed), 10);
                  ConstantInt* min = ConstantInt::get(IntegerType::get(F.getContext(), bits*2), getMin(bits, is_signed), 10);
                  CmpInst::Predicate max_cmp = (is_signed ? CmpInst::ICMP_SGT : CmpInst::ICMP_UGT);
                  CmpInst::Predicate min_cmp = (is_signed ? CmpInst::ICMP_SLT : CmpInst::ICMP_ULT);
                  ICmpInst* gt = new ICmpInst(&*I, max_cmp, ai, max, "");
                  ICmpInst* lt = new ICmpInst(&*I, min_cmp, ai, min, "");
                  flag = BinaryOperator::Create(Instruction::Or, gt, lt, "", &*I);

                  // Check for an overflow
                  ArrayRef<Value*> check_overflow_args(CastInst::CreateIntegerCast(flag, co->arg_begin()->getType(), false, "", &*I));
                  CallInst::Create(co, check_overflow_args, "", &*I);

                  // Block paths after an assertion failure
                  ArrayRef<Value*> assume_args(CastInst::CreateIntegerCast(BinaryOperator::CreateNot(flag, "", &*I),
                        verif_assume->arg_begin()->getType(), false, "", &*I));
                  CallInst::Create(verif_assume, assume_args, "", &*I);

                } else {
                  ConstantInt* a = ConstantInt::getFalse(F.getContext());
                  flag = BinaryOperator::Create(Instruction::And, a, a, "", &*I);
                }
                I->replaceAllUsesWith(flag);
              }
            }
          }
        }
        if (auto sdi = dyn_cast<BinaryOperator>(&*I)) {
          if (sdi->getOpcode() == Instruction::SDiv) {
            int bits = sdi->getType()->getIntegerBitWidth();
            Value* o1 = sdi->getOperand(0);
            Value* o2 = sdi->getOperand(1);
            CastInst* so1 = CastInst::CreateSExtOrBitCast(o1, IntegerType::get(F.getContext(), bits*2), "", &*I);
            CastInst* so2 = CastInst::CreateSExtOrBitCast(o2, IntegerType::get(F.getContext(), bits*2), "", &*I);
            BinaryOperator* lsdi = BinaryOperator::Create(Instruction::SDiv, so1, so2, "", &*I);
            ConstantInt* max = ConstantInt::get(IntegerType::get(F.getContext(), bits*2), getMax(bits, true), 10);
            ConstantInt* min = ConstantInt::get(IntegerType::get(F.getContext(), bits*2), getMin(bits, true), 10);
            ICmpInst* gt = new ICmpInst(&*I, CmpInst::ICMP_SGT, lsdi, max, "");
            ICmpInst* lt = new ICmpInst(&*I, CmpInst::ICMP_SLT, lsdi, min, "");
            BinaryOperator* flag = BinaryOperator::Create(Instruction::Or, gt, lt, "", &*I);
            CastInst* tf = CastInst::CreateSExtOrBitCast(flag, co->getArgumentList().begin()->getType(), "", &*I);
            CallInst::Create(co, {tf}, "", &*I);
            CastInst* tv = CastInst::CreateTruncOrBitCast(lsdi, sdi->getType(), "", &*I);
            (*I).replaceAllUsesWith(tv);
          }
        }
      }
    }
  }
  for (auto I : inst_to_remove) {
    I->removeFromParent();
  }
  return true;
}

// Pass ID variable
char IntegerOverflowChecker::ID = 0;

const char* IntegerOverflowChecker::getPassName() const {
  return "Checked integer arithmetic intrinsics";
}
}
