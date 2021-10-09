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

Optional<APInt> getConstantIntValue(const Value *V) {
  if (const ConstantInt *ci = dyn_cast<ConstantInt>(V)) {
    const APInt &value = ci->getValue();
    return Optional<APInt>(value);
  } else {
    return Optional<APInt>();
  }
}

bool isConstantInt(const Value *V) {
  Optional<APInt> constantValue = getConstantIntValue(V);
  return constantValue.hasValue() && (*constantValue + 1).isPowerOf2();
}

bool RewriteBitwiseOps::runOnModule(Module &m) {
  std::vector<Instruction *> instsFrom;
  std::vector<Instruction *> instsTo;

  for (auto &F : m) {
    if (Naming::isSmackName(F.getName()))
      continue;
    for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
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
          } else
            llvm_unreachable("Unexpected shift operation!");

          auto lhs = bi->getOperand(0);
          unsigned bitWidth = getOpBitWidth(lhs);
          APInt rhsVal = APInt(bitWidth, "1", 10);
          const APInt &value = ci->getValue();
          rhsVal <<= value;
          Value *rhs = ConstantInt::get(ci->getType(), rhsVal);
          Instruction *replacement = BinaryOperator::Create(op, lhs, rhs, "");
          instsFrom.push_back(&*I);
          instsTo.push_back(replacement);
        }
      } else if (I->isBitwiseLogicOp()) {
        // If the operation is a bit-wise `and' and the mask variable is
        // constant, it may be possible to replace this operation with a
        // remainder operation. If one argument has only ones, and they're only
        // in the least significant bit, then the mask is 2^(number of ones)
        // - 1. This is equivalent to the remainder when dividing by 2^(number
        // of ones).
        BinaryOperator *bi = cast<BinaryOperator>(&*I);
        unsigned opcode = bi->getOpcode();
        if (opcode == Instruction::And) {
          Value *args[] = {bi->getOperand(0), bi->getOperand(1)};
          int maskOperand = -1;

          if (isConstantInt(args[0])) {
            maskOperand = 0;
          }
          // Zvonimir: Right-side constants do not work well on SVCOMP
          // } else if (isConstantInt(args[1])) {
          //   maskOperand = 1;
          // }

          if (maskOperand == -1) {
            unsigned bitWidth = getOpBitWidth(&*I);
            Function *co;
            if (bitWidth == 64) {
              co = m.getFunction("__SMACK_and64");
            } else if (bitWidth == 32) {
              co = m.getFunction("__SMACK_and32");
            } else if (bitWidth == 16) {
              co = m.getFunction("__SMACK_and16");
            } else if (bitWidth == 8) {
              co = m.getFunction("__SMACK_and8");
            } else {
              continue;
            }
            assert(co != NULL && "Function __SMACK_and should be present.");
            std::vector<Value *> args;
            args.push_back(bi->getOperand(0));
            args.push_back(bi->getOperand(1));
            instsFrom.push_back(&*I);
            instsTo.push_back(CallInst::Create(co, args, ""));
          } else {
            auto lhs = args[1 - maskOperand];
            Value *rhs = ConstantInt::get(
                m.getContext(), *getConstantIntValue(args[maskOperand]) + 1);
            Instruction *replacement =
                BinaryOperator::Create(Instruction::URem, lhs, rhs, "");
            instsFrom.push_back(&*I);
            instsTo.push_back(replacement);
          }
        } else if (opcode == Instruction::Or) {
          unsigned bitWidth = getOpBitWidth(&*I);
          Function *co;
          if (bitWidth == 64) {
            co = m.getFunction("__SMACK_or64");
          } else if (bitWidth == 32) {
            co = m.getFunction("__SMACK_or32");
          } else if (bitWidth == 16) {
            co = m.getFunction("__SMACK_or16");
          } else if (bitWidth == 8) {
            co = m.getFunction("__SMACK_or8");
          } else {
            continue;
          }
          assert(co != NULL && "Function __SMACK_or should be present.");
          std::vector<Value *> args;
          args.push_back(bi->getOperand(0));
          args.push_back(bi->getOperand(1));
          instsFrom.push_back(&*I);
          instsTo.push_back(CallInst::Create(co, args, ""));
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
  return "Translate bitwise operations with constant arguments to integer "
         "operations";
}
} // namespace smack
