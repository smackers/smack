//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/IntegerOverflowChecker.h"
#include "smack/Naming.h"
#include "llvm/IR/Module.h"
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

const std::map<std::string, Instruction::BinaryOps> IntegerOverflowChecker::INSTRUCTION_TABLE {
  {"add", Instruction::Add},
  {"sub", Instruction::Sub},
  {"mul", Instruction::Mul}
};

std::string getMax(unsigned bits, bool isSigned) {
  if (isSigned) {
    return APInt::getSignedMaxValue(bits).toString(10, true);
  } else {
    return APInt::getMaxValue(bits).toString(10, false);
  }
}

std::string getMin(unsigned bits, bool isSigned) {
  if (isSigned) {
    return APInt::getSignedMinValue(bits).toString(10, true);
  } else {
    return APInt::getMinValue(bits).toString(10, false);
  }
}

Value* IntegerOverflowChecker::extValue(Value* v, int bits, bool isSigned, Instruction* i, bool check) {
  if (check) {
    if (isSigned) {
      return CastInst::CreateSExtOrBitCast(v, IntegerType::get(i->getFunction()->getContext(), bits*2), "", i);
    } else {
      return CastInst::CreateZExtOrBitCast(v, IntegerType::get(i->getFunction()->getContext(), bits*2), "", i);
    }
  } else
    return v;
}

BinaryOperator* IntegerOverflowChecker::mkFlag(Value* v, int bits, bool isSigned, Instruction* i, bool check) {
  if (check) {
    ConstantInt* max = ConstantInt::get(IntegerType::get(i->getFunction()->getContext(), bits*2), getMax(bits, isSigned), 10);
    ConstantInt* min = ConstantInt::get(IntegerType::get(i->getFunction()->getContext(), bits*2), getMin(bits, isSigned), 10);
    CmpInst::Predicate maxCmpPred = (isSigned ? CmpInst::ICMP_SGT : CmpInst::ICMP_UGT);
    CmpInst::Predicate minCmpPred = (isSigned ? CmpInst::ICMP_SLT : CmpInst::ICMP_ULT);
    ICmpInst* gt = new ICmpInst(i, maxCmpPred, v, max, "");
    ICmpInst* lt = new ICmpInst(i, minCmpPred, v, min, "");
    return BinaryOperator::Create(Instruction::Or, gt, lt, "", i);
  } else {
    ConstantInt* a = ConstantInt::getFalse(i->getFunction()->getContext());
    return BinaryOperator::Create(Instruction::And, a, a, "", i);
  }
}

Value* IntegerOverflowChecker::mkResult(Value* v, int bits, Instruction* i, bool check) {
  if (check)
    return CastInst::CreateTruncOrBitCast(v, IntegerType::get(i->getFunction()->getContext(), bits), "", i);
  else
    return v;
}

void IntegerOverflowChecker::mkCheck(Function* co, BinaryOperator* flag, Instruction* i) {
  ArrayRef<Value*> args(CastInst::CreateIntegerCast(flag, co->arg_begin()->getType(), false, "", i));
  CallInst::Create(co, args, "", i);
}

void IntegerOverflowChecker::mkBlockingAssume(Function* va, BinaryOperator* flag, Instruction* i) {
  ArrayRef<Value*> args(CastInst::CreateIntegerCast(BinaryOperator::CreateNot(flag, "", i),
        va->arg_begin()->getType(), false, "", i));
  CallInst::Create(va, args, "", i);
}

bool IntegerOverflowChecker::runOnModule(Module& m) {
  Function* co = m.getFunction("__SMACK_check_overflow");
  assert(co != NULL && "Function __SMACK_check_overflow should be present.");
  Function* va = m.getFunction("__VERIFIER_assume");
  assert(va != NULL && "Function __VERIFIER_assume should be present.");
  std::vector<Instruction*> instToRemove;
  for (auto& F : m) {
    if (!Naming::isSmackName(F.getName())) {
      for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
        if (auto ei = dyn_cast<ExtractValueInst>(&*I)) {
          if (auto ci = dyn_cast<CallInst>(ei->getAggregateOperand())) {
            Function* f = ci->getCalledFunction();
            SmallVectorImpl<StringRef> *ar = new SmallVector<StringRef, 3>;
            if (f && f->hasName() && OVERFLOW_INTRINSICS.match(f->getName().str(), ar)) {
              if (ei->getIndices()[0] == 1) {
                Instruction* prev = &*std::prev(I);
                bool isSigned = ar->begin()[1].str() == "s";
                std::string op = ar->begin()[2].str();
                std::string len = ar->begin()[3].str();
                int bits = std::stoi(len);
                Value* eo1 = extValue(ci->getArgOperand(0), bits, isSigned, &*I, SmackOptions::IntegerOverflow);
                Value* eo2 = extValue(ci->getArgOperand(1), bits, isSigned, &*I, SmackOptions::IntegerOverflow);
                BinaryOperator* ai = BinaryOperator::Create(INSTRUCTION_TABLE.at(op), eo1, eo2, "", &*I);
                if (prev && isa<ExtractValueInst>(prev)) {
                  ExtractValueInst* pei = cast<ExtractValueInst>(prev);
                  if (auto pci = dyn_cast<CallInst>(pei->getAggregateOperand())) {
                    if (pci == ci) {
                      Value* r = mkResult(ai, bits, &*I, SmackOptions::IntegerOverflow);
                      prev->replaceAllUsesWith(r);
                      instToRemove.push_back(prev);
                    }
                  }
                }
                BinaryOperator* flag = mkFlag(ai, bits, isSigned, &*I, SmackOptions::IntegerOverflow);
                mkCheck(co, flag, &*I);
                mkBlockingAssume(va, flag, &*I);
                I->replaceAllUsesWith(flag);
                instToRemove.push_back(&*I);
              }
            }
          }
        }
        if (auto sdi = dyn_cast<BinaryOperator>(&*I)) {
          if (sdi->getOpcode() == Instruction::SDiv && SmackOptions::IntegerOverflow) {
            int bits = sdi->getType()->getIntegerBitWidth();
            Value* eo1 = extValue(sdi->getOperand(0), bits, true, &*I);
            Value* eo2 = extValue(sdi->getOperand(1), bits, true, &*I);
            BinaryOperator* lsdi = BinaryOperator::Create(Instruction::SDiv, eo1, eo2, "", &*I);
            BinaryOperator* flag = mkFlag(lsdi, bits, true, &*I, smack::SmackOptions::IntegerOverflow);
            mkCheck(co, flag, &*I);
            Value* r = mkResult(lsdi, bits, &*I);
            I->replaceAllUsesWith(r);
            instToRemove.push_back(&*I);
          }
        }
      }
    }
  }
  for (auto I : instToRemove) {
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
