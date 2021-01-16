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
#include <unordered_map>
#include <utility>

namespace smack {

using namespace llvm;
using SC = RewriteBitwiseOps::SpecialCase;

unsigned getOpBitWidth(const Value *V) {
  const Type *T = V->getType();
  const IntegerType *iType = cast<const IntegerType>(T);
  return iType->getBitWidth();
}

int getConstOpId(const Instruction *i) {
  return llvm::isa<ConstantInt>(i->getOperand(1))
             ? 1
             : (llvm::isa<ConstantInt>(i->getOperand(0)) ? 0 : -1);
}

Instruction *RewriteBitwiseOps::rewriteShift(Instruction::BinaryOps newOp,
                                             Instruction *i) {
  auto ci = llvm::cast<ConstantInt>(i->getOperand(1));
  auto lhs = i->getOperand(0);
  unsigned bitWidth = getOpBitWidth(lhs);
  APInt rhsVal = APInt(bitWidth, "1", 10);
  const APInt &value = ci->getValue();
  rhsVal <<= value;
  Value *rhs = ConstantInt::get(ci->getType(), rhsVal);
  return BinaryOperator::Create(newOp, lhs, rhs, "", i);
}

Instruction *RewriteBitwiseOps::rewriteShr(Instruction *i) {
  // Shifting right by a constant amount is equivalent to dividing by
  // 2^amount
  return rewriteShift(Instruction::SDiv, i);
}

Instruction *RewriteBitwiseOps::rewriteShl(Instruction *i) {
  // Shifting left by a constant amount is equivalent to dividing by
  // 2^amount
  return rewriteShift(Instruction::Mul, i);
}

Instruction *RewriteBitwiseOps::rewriteAndPoTMO(Instruction *i) {
  // If the operation is a bit-wise `and' and the mask variable is
  // constant, it may be possible to replace this operation with a
  // remainder operation. If one argument has only ones, and they're only
  // in the least significant bit, then the mask is 2^(number of ones)
  // - 1. This is equivalent to the remainder when dividing by 2^(number
  // of ones).
  // Zvonimir: Right-side constants do not work well on SVCOMP
  // } else if (isConstantInt(args[1])) {
  //   maskOperand = 1;
  // }
  auto constOpId = getConstOpId(i);
  auto constVal =
      (llvm::cast<ConstantInt>(i->getOperand(constOpId)))->getValue();
  auto lhs = i->getOperand(1 - constOpId);
  Value *rhs = ConstantInt::get(i->getContext(), constVal + 1);
  return BinaryOperator::Create(Instruction::URem, lhs, rhs, "", i);
}

Instruction *RewriteBitwiseOps::rewriteAndNPot(Instruction *i) {
  // E.g., rewrite ``x && -32'' into ``x - x % 32''
  auto constOpId = getConstOpId(i);
  auto constVal =
      (llvm::cast<ConstantInt>(i->getOperand(constOpId)))->getValue();
  auto lhs = i->getOperand(1 - constOpId);
  auto rem = BinaryOperator::Create(
      Instruction::URem, lhs, ConstantInt::get(i->getContext(), 0 - constVal),
      "", i);
  return BinaryOperator::Create(Instruction::Sub, lhs, rem, "", i);
}

boost::optional<SC> RewriteBitwiseOps::getSpecialCase(Instruction *i) {
  if (auto bi = dyn_cast<BinaryOperator>(i)) {
    auto opcode = bi->getOpcode();
    if (bi->isShift() && llvm::isa<ConstantInt>(bi->getOperand(1))) {
      if (opcode == Instruction::AShr || opcode == Instruction::LShr)
        return SC::Shr;
      else if (opcode == Instruction::Shl)
        return SC::Shl;
    } else if (opcode == Instruction::And) {
      auto constOpId = getConstOpId(i);
      if (constOpId >= 0) {
        auto val =
            (llvm::cast<ConstantInt>(i->getOperand(constOpId)))->getValue();
        if ((val + 1).isPowerOf2())
          return SC::AndPoTMO;
        else if ((0 - val).isPowerOf2())
          return SC::AndNPoT;
      }
    }
  }
  return boost::none;
}

Instruction *RewriteBitwiseOps::rewriteSpecialCase(SC sc, Instruction *i) {
  static std::unordered_map<SC, Instruction *(*)(Instruction *)> table{
      {SC::Shr, &rewriteShr},
      {SC::Shl, &rewriteShl},
      {SC::AndPoTMO, &rewriteAndPoTMO},
      {SC::AndNPoT, &rewriteAndNPot}};
  return table[sc](i);
}

boost::optional<Instruction *>
RewriteBitwiseOps::rewriteGeneralCase(Instruction *i) {
  auto opCode = i->getOpcode();
  if (opCode != Instruction::And && opCode != Instruction::Or)
    return boost::none;
  unsigned bitWidth = getOpBitWidth(i);
  if (bitWidth > 64 || bitWidth < 8 || (bitWidth & (bitWidth - 1)))
    return boost::none;
  std::string func =
      std::string("__SMACK_") + i->getOpcodeName() + std::to_string(bitWidth);
  Function *co = i->getModule()->getFunction(func);
  assert(co != NULL && "Function __SMACK_[and|or] should be present.");
  std::vector<Value *> args;
  args.push_back(i->getOperand(0));
  args.push_back(i->getOperand(1));
  return CallInst::Create(co, args, "", i);
}

bool RewriteBitwiseOps::runOnModule(Module &m) {
  std::vector<std::pair<Instruction *, Instruction *>> insts;

  for (auto &F : m) {
    if (Naming::isSmackName(F.getName()))
      continue;
    for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
      Instruction *i = &*I;
      if (auto sc = getSpecialCase(i))
        insts.push_back(std::make_pair(i, rewriteSpecialCase(*sc, i)));
      else if (auto oi = rewriteGeneralCase(i))
        insts.push_back(std::make_pair(i, *oi));
    }
  }

  for (auto &p : insts) {
    p.first->replaceAllUsesWith(p.second);
    p.first->removeFromParent();
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
