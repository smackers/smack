//
// This file is distributed under the MIT License. See LICENSE for details.
//

//
// This pass converts LLVM's checked integer-arithmetic operations into basic
// operations, and optionally allows for the checking of overflow.
//

#define DEBUG_TYPE "smack-overflow"
#include "smack/IntegerOverflowChecker.h"
#include "smack/Debug.h"
#include "smack/Naming.h"
#include "smack/SmackOptions.h"
#include "llvm/ADT/APInt.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/ValueSymbolTable.h"
#include "llvm/Support/Regex.h"
#include <string>

namespace smack {

using namespace llvm;

Regex OVERFLOW_INTRINSICS("^llvm.(u|s)(add|sub|mul).with.overflow.i([0-9]+)$");

const std::map<std::string, Instruction::BinaryOps>
    IntegerOverflowChecker::INSTRUCTION_TABLE{{"add", Instruction::Add},
                                              {"sub", Instruction::Sub},
                                              {"mul", Instruction::Mul}};

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
Value *IntegerOverflowChecker::extendBitWidth(Value *v, int bits, bool isSigned,
                                              Instruction *i) {
  if (isSigned)
    return CastInst::CreateSExtOrBitCast(
        v, IntegerType::get(i->getFunction()->getContext(), bits * 2), "", i);
  else
    return CastInst::CreateZExtOrBitCast(
        v, IntegerType::get(i->getFunction()->getContext(), bits * 2), "", i);
}

/*
 * Generates instructions to determine whether a Value v is is out of range for
 * its bit width and sign.
 */
BinaryOperator *IntegerOverflowChecker::createFlag(Value *v, int bits,
                                                   bool isSigned,
                                                   Instruction *i) {
  ConstantInt *max = ConstantInt::get(
      IntegerType::get(i->getFunction()->getContext(), bits * 2),
      getMax(bits, isSigned), 10);
  ConstantInt *min = ConstantInt::get(
      IntegerType::get(i->getFunction()->getContext(), bits * 2),
      getMin(bits, isSigned), 10);
  CmpInst::Predicate maxCmpPred =
      (isSigned ? CmpInst::ICMP_SGT : CmpInst::ICMP_UGT);
  CmpInst::Predicate minCmpPred =
      (isSigned ? CmpInst::ICMP_SLT : CmpInst::ICMP_ULT);
  ICmpInst *gt = new ICmpInst(i, maxCmpPred, v, max, "");
  ICmpInst *lt = new ICmpInst(i, minCmpPred, v, min, "");
  return BinaryOperator::Create(Instruction::Or, gt, lt, "", i);
}

/*
 * Create an instruction to cast v to bits size.
 */
Value *IntegerOverflowChecker::createResult(Value *v, int bits,
                                            Instruction *i) {
  return CastInst::CreateTruncOrBitCast(
      v, IntegerType::get(i->getFunction()->getContext(), bits), "", i);
}

/*
 * This adds a call instruction to __SMACK_check_overflow to determine if an
 * overflow occured as indicated by flag.
 */
void IntegerOverflowChecker::addCheck(Function *co, Value *flag,
                                      Instruction *i) {
  Value *args = CastInst::CreateIntegerCast(flag, co->arg_begin()->getType(),
                                            false, "", i);
  CallInst::Create(co, args, "", i);
}

/*
 * This inserts a call to assume with flag negated to prevent the verifier
 * from exploring paths past a __SMACK_check_overflow
 */
void IntegerOverflowChecker::addBlockingAssume(Function *va, Value *flag,
                                               Instruction *i) {
  Value *args =
      CastInst::CreateIntegerCast(BinaryOperator::CreateNot(flag, "", i),
                                  va->arg_begin()->getType(), false, "", i);
  CallInst::Create(va, args, "", i);
}

bool IntegerOverflowChecker::runOnModule(Module &m) {
  Function *co = m.getFunction("__SMACK_check_overflow");
  assert(co != NULL && "Function __SMACK_check_overflow should be present.");
  Function *va = m.getFunction("__VERIFIER_assume");
  assert(va != NULL && "Function __VERIFIER_assume should be present.");
  std::vector<Instruction *> instToErase;
  for (auto &F : m) {
    if (Naming::isSmackName(F.getName()))
      continue;
    for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
      if (auto ci = dyn_cast<CallInst>(&*I)) {
        Function *f = ci->getCalledFunction();
        if (f && f->hasName()) {
          auto fn = f->getName();
          if (fn.find("__ubsan_handle_shift_out_of_bounds") !=
                  StringRef::npos ||
              fn.find("__ubsan_handle_divrem_overflow") != StringRef::npos) {
            // If the call to __ubsan_handle_* is reachable,
            // then an overflow is possible.
            if (SmackOptions::IntegerOverflow) {
              // Add check for UBSan left shift/signed division when needed
              ConstantInt *flag =
                  ConstantInt::getTrue(ci->getFunction()->getContext());
              if (SmackOptions::shouldCheckFunction(F.getName()))
                addCheck(co, flag, ci);
              addBlockingAssume(va, flag, ci);
              ci->replaceAllUsesWith(flag);
              instToErase.push_back(ci);
            }
          }
          SmallVector<StringRef, 4> info;
          if (OVERFLOW_INTRINSICS.match(fn, &info)) {
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
            SDEBUG(errs() << "Processing intrinsic: " << fn << "\n");
            assert(info.size() == 4 && "Must capture three matched strings.");
            bool isSigned = (info[1] == "s");
            std::string op = info[2].str();
            unsigned bits = 0;
            auto res = info[3].getAsInteger(10, bits);
            assert(!res && "Invalid bit widths.");
            Value *eo1 =
                extendBitWidth(ci->getArgOperand(0), bits, isSigned, ci);
            Value *eo2 =
                extendBitWidth(ci->getArgOperand(1), bits, isSigned, ci);
            SDEBUG(errs() << "Processing operator: " << op << "\n");
            assert(INSTRUCTION_TABLE.count(op) != 0 &&
                   "Operator must be present in our instruction table.");
            BinaryOperator *ai = BinaryOperator::Create(
                INSTRUCTION_TABLE.at(op), eo1, eo2, "", ci);
            Value *r = createResult(ai, bits, &*I);
            BinaryOperator *flag = createFlag(ai, bits, isSigned, ci);
            if (SmackOptions::IntegerOverflow &&
                SmackOptions::shouldCheckFunction(F.getName()))
              addCheck(co, flag, ci);
            for (auto U : ci->users()) {
              if (ExtractValueInst *ei = dyn_cast<ExtractValueInst>(U)) {
                if (ei->getNumIndices() == 1) {
                  if (ei->getIndices()[0] == 0)
                    // value part
                    ei->replaceAllUsesWith(r);
                  else if (ei->getIndices()[0] == 1) {
                    // flag part
                    // addBlockingAssume(va, flag, ei);
                    ei->replaceAllUsesWith(flag);
                  } else
                    llvm_unreachable("Unexpected extractvalue inst!");
                  instToErase.push_back(ei);
                }
              }
            }
            instToErase.push_back(ci);
          }
        }
      }
    }
  }
  for (auto I : instToErase) {
    I->eraseFromParent();
  }
  return true;
}

// Pass ID variable
char IntegerOverflowChecker::ID = 0;

StringRef IntegerOverflowChecker::getPassName() const {
  return "Checked integer arithmetic intrinsics";
}
} // namespace smack
