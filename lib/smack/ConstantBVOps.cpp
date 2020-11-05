//
// This file is distributed under the MIT License. See LICENSE for details.
//

// This pass converts bitwise operations with certain constant operands
// into equivalent integer operations.

#include "smack/ConstantBVOps.h"
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
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include <string>

namespace smack {

using namespace llvm;

unsigned getOpWidth(const Value *t) {
  Type *type = t->getType();
  IntegerType *iType = dyn_cast<IntegerType>(type);
  return iType->getBitWidth();
}

bool ConstantBVOps::runOnFunction(Function &f) {
  std::vector<Instruction *> instsFrom;
  std::vector<Instruction *> instsTo;
  if (Naming::isSmackName(f.getName()))
    return false;
  for (inst_iterator I = inst_begin(f), E = inst_end(f); I != E; ++I) {
    if (I->isShift()) {
      BinaryOperator *bi = dyn_cast<BinaryOperator>(&*I);
      Value *amt = bi->getOperand(1);
      if (ConstantInt *ci = dyn_cast<ConstantInt>(amt)) {
        const APInt &value = ci->getValue();
        unsigned opcode = bi->getOpcode();
        Instruction::BinaryOps op;
        if (opcode == Instruction::AShr || opcode == Instruction::LShr) {
          // Shifting right by a constant amount is equivalent to dividing by
          // 2^amt
          op = Instruction::SDiv;
        } else if (opcode == Instruction::Shl) {
          // Shifting left by a constant amount is equivalent to dividing by
          // 2^amt
          op = Instruction::Mul;
        }
        auto lhs = bi->getOperand(0);
        unsigned bw = getOpWidth(lhs);
        APInt rhsVal = APInt(bw, "1", 10);
        rhsVal <<= value;
        Value *rhs = ConstantInt::get(ci->getType(), rhsVal);
        Instruction *replacement =
            BinaryOperator::Create(op, lhs, rhs, "", (Instruction *)nullptr);
        instsFrom.push_back(&*I);
        instsTo.push_back(replacement);
      }
    }
    if (I->isBitwiseLogicOp()) {
      // If the operation is a bit-wise `and' and the mask variable is constant,
      // it may be possible to replace this operation with a remainder
      // operation. If the rhs has only ones, and they're only in the least
      // significant bit, then the mask is 2^(number of ones) - 1. This is
      // equivalent to the remainder when dividing by 2^(number of ones).
      BinaryOperator *bi = dyn_cast<BinaryOperator>(&*I);
      Value *mask = bi->getOperand(1);
      if (ConstantInt *ci = dyn_cast<ConstantInt>(mask)) {
        const APInt &value = ci->getValue();
        unsigned opcode = bi->getOpcode();
        if (opcode == Instruction::And) {
          if ((value + 1).isPowerOf2()) {
            auto lhs = bi->getOperand(0);
            Value *rhs = ConstantInt::get(ci->getType(), (value + 1));
            Instruction *replacement = BinaryOperator::Create(
                Instruction::URem, lhs, rhs, "", (Instruction *)nullptr);
            instsFrom.push_back(&*I);
            instsTo.push_back(replacement);
          }
        }
      }
    }
  }

  for (size_t i = 0; i < instsFrom.size(); i++) {
    ReplaceInstWithInst(instsFrom[i], instsTo[i]);
  }

  return true;
}

// Pass ID variable
char ConstantBVOps::ID = 0;

StringRef ConstantBVOps::getPassName() const {
  return "Translate BV ops with constant arguments to integer operations";
}
} // namespace smack
