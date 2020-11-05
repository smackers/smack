//
// This file is distributed under the MIT License. See LICENSE for details.
//

// This pass converts bitwise operations with certain constant operands
// into equivalent integer operations.

#include "smack/RewriteBitwiseOps.h"
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

unsigned getOpBitWidth(const Value *V) {
  const Type *T = V->getType();
  const IntegerType *iType = cast<IntegerType>(T);
  return iType->getBitWidth();
}

bool RewriteBitwiseOps::runOnFunction(Function &f) {
  if (SmackOptions::BitPrecise || SmackOptions::BitPrecisePointers)
    // Do not run this pass in bitvector mode.
    return false;
  if (Naming::isSmackName(f.getName()))
    return false;

  std::vector<Instruction *> instsFrom;
  std::vector<Instruction *> instsTo;

  for (inst_iterator I = inst_begin(f), E = inst_end(f); I != E; ++I) {
    if (I->isShift()) {
      BinaryOperator *bi = cast<BinaryOperator>(&*I);
      Value *amount = bi->getOperand(1);

      if (ConstantInt *ci = dyn_cast<ConstantInt>(amount)) {
        unsigned opcode = bi->getOpcode();
        Instruction::BinaryOps op;
        if (opcode == Instruction::AShr || opcode == Instruction::LShr) {
          // Shifting right by a constant amount is equivalent to dividing by
          // 2^amount
          op = Instruction::SDiv;
        } else if (opcode == Instruction::Shl) {
          // Shifting left by a constant amount is equivalent to dividing by
          // 2^amount
          op = Instruction::Mul;
        }

        auto lhs = bi->getOperand(0);
        unsigned bitWidth = getOpBitWidth(lhs);
        APInt rhsVal = APInt(bitWidth, "1", 10);
        const APInt &value = ci->getValue();
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
      BinaryOperator *bi = cast<BinaryOperator>(&*I);
      Value *mask = bi->getOperand(1);
      if (ConstantInt *ci = dyn_cast<ConstantInt>(mask)) {
        unsigned opcode = bi->getOpcode();
        if (opcode == Instruction::And) {
	    const APInt &value = ci->getValue();
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

  for (size_t i = 0; i < instsFrom.size(); ++i) {
    ReplaceInstWithInst(instsFrom[i], instsTo[i]);
  }

  return true;
}

// Pass ID variable
char RewriteBitwiseOps::ID = 0;

StringRef RewriteBitwiseOps::getPassName() const {
  return "Translate bitwise operations with constant arguments to integer operations";
}
} // namespace smack
