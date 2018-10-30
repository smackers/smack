//
// This file is distributed under the MIT License. See LICENSE for details.
//

//
// This pass converts LLVM's checked integer-arithmetic operations into basic
// operations, and optionally allows for the checking of overflow.
//

#define DEBUG_TYPE "smack-overflow"
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

std::string IntegerOverflowChecker::getMax(unsigned bits, bool isSigned) {
  if (isSigned)
    return APInt::getSignedMaxValue(bits).toString(10, true);
  else
    return APInt::getMaxValue(bits).toString(10, false);
}

std::string IntegerOverflowChecker::getMin(unsigned bits, bool isSigned) {
  if (isSigned)
    return APInt::getSignedMinValue(bits).toString(10, true);
  else
    return APInt::getMinValue(bits).toString(10, false);
}

/*
 * Optionally generates a double wide version of v for the purpose of detecting
 * overflow.
 */
Value* IntegerOverflowChecker::extendBitWidth(Value* v, int bits, bool isSigned, Instruction* i) {
  if (SmackOptions::IntegerOverflow) {
    if (isSigned)
      return CastInst::CreateSExtOrBitCast(v, IntegerType::get(i->getFunction()->getContext(), bits*2), "", i);
    else
      return CastInst::CreateZExtOrBitCast(v, IntegerType::get(i->getFunction()->getContext(), bits*2), "", i);
  } else
    return v;
}

/*
 * Generates instructions to determine whether a Value v is is out of range for
 * its bit width and sign.
 */
BinaryOperator* IntegerOverflowChecker::createFlag(Value* v, int bits, bool isSigned, Instruction* i) {
  if (SmackOptions::IntegerOverflow) {
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

/*
 * Create an instruction to cast v to bits size.
 */
Value* IntegerOverflowChecker::createResult(Value* v, int bits, Instruction* i) {
  if (SmackOptions::IntegerOverflow)
    return CastInst::CreateTruncOrBitCast(v, IntegerType::get(i->getFunction()->getContext(), bits), "", i);
  else
    return v;
}

/*
 * This adds a call instruction to __SMACK_check_overflow to determine if an
 * overflow occured as indicated by flag.
 */
void IntegerOverflowChecker::addCheck(Function* co, BinaryOperator* flag, Instruction* i) {
  ArrayRef<Value*> args(CastInst::CreateIntegerCast(flag, co->arg_begin()->getType(), false, "", i));
  CallInst::Create(co, args, "", i);
}

/*
 * This inserts a call to assume with flag negated to prevent the verifier
 * from exploring paths past a __SMACK_check_overflow
 */
void IntegerOverflowChecker::addBlockingAssume(Function* va, BinaryOperator* flag, Instruction* i) {
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
    if (Naming::isSmackName(F.getName()))
      continue;
    for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
      if (auto ei = dyn_cast<ExtractValueInst>(&*I)) {
        if (auto ci = dyn_cast<CallInst>(ei->getAggregateOperand())) {
          Function* f = ci->getCalledFunction();
          SmallVector<StringRef, 4> info;
          if (f && f->hasName() && OVERFLOW_INTRINSICS.match(f->getName(), &info)
              && ei->getIndices()[0] == 1) {
            /*
             * If ei is an ExtractValueInst whose value flows from an LLVM
             * checked value intrinsic f, then we do the following:
             * - The intrinsic is replaced with the non-intrinsic version of the
             *   operation.
             * - If checking is enabled, the operation is computed in double bit
             *   width.
             * - A flag is computed to determine whether an overflow occured.
             * - The overflow flag is optionally checked to raise an
             *   integer-overflow assertion violation.
             * - Finally, an assumption about the value of the flag is created
             *   to block erroneous checking of paths after the overflow check.
             */
            DEBUG(errs() << "Processing intrinsic: " << f->getName().str() << "\n");
            assert(info.size() == 4 && "Must capture three matched strings.");
            bool isSigned = (info[1] == "s");
            std::string op = info[2];
            int bits = std::stoi(info[3]);
            Instruction* prev = &*std::prev(I);
            Value* eo1 = extendBitWidth(ci->getArgOperand(0), bits, isSigned, &*I);
            Value* eo2 = extendBitWidth(ci->getArgOperand(1), bits, isSigned, &*I);
            DEBUG(errs() << "Processing operator: " << op << "\n");
            assert(INSTRUCTION_TABLE.count(op) != 0 && "Operator must be present in our instruction table.");
            BinaryOperator* ai = BinaryOperator::Create(INSTRUCTION_TABLE.at(op), eo1, eo2, "", &*I);
            if (auto pei = dyn_cast_or_null<ExtractValueInst>(prev)) {
              if (ci == dyn_cast<CallInst>(pei->getAggregateOperand())) {
                Value* r = createResult(ai, bits, &*I);
                prev->replaceAllUsesWith(r);
                instToRemove.push_back(prev);
              }
            }
            BinaryOperator* flag = createFlag(ai, bits, isSigned, &*I);
            if (SmackOptions::IntegerOverflow)
              addCheck(co, flag, &*I);
            addBlockingAssume(va, flag, &*I);
            I->replaceAllUsesWith(flag);
            instToRemove.push_back(&*I);
          }
        }
      }
      if (auto sdi = dyn_cast<BinaryOperator>(&*I)) {
        if (sdi->getOpcode() == Instruction::SDiv && SmackOptions::IntegerOverflow) {
          int bits = sdi->getType()->getIntegerBitWidth();
          Value* eo1 = extendBitWidth(sdi->getOperand(0), bits, true, &*I);
          Value* eo2 = extendBitWidth(sdi->getOperand(1), bits, true, &*I);
          BinaryOperator* lsdi = BinaryOperator::Create(Instruction::SDiv, eo1, eo2, "", &*I);
          BinaryOperator* flag = createFlag(lsdi, bits, true, &*I);
          addCheck(co, flag, &*I);
          Value* r = createResult(lsdi, bits, &*I);
          I->replaceAllUsesWith(r);
          instToRemove.push_back(&*I);
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
