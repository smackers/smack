//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/SignedIntegerOverflowChecker.h"
#include "smack/Naming.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Constants.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/ValueSymbolTable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/Regex.h"

namespace smack {

using namespace llvm;

Regex OVERFLOW_INTRINSICS("^llvm.s(add|sub|mul).with.overflow.i32$");

std::map<std::string, Instruction::BinaryOps> SignedIntegerOverflowChecker::INSTRUCTION_TABLE {
  {"add", Instruction::Add},
  {"sub", Instruction::Sub},
  {"mul", Instruction::Mul}
};

void SignedIntegerOverflowChecker::replaceValue(Value* ee, Value* er) {
  for (auto u : ee->users()) {
    if (auto inst = dyn_cast<Instruction>(u)) {
      if (inst != cast<Instruction>(ee)) {
        for (unsigned i = 0; i < inst->getNumOperands(); ++i) {
          if (inst->getOperand(i) == ee)
            inst->setOperand(i, er);
        }
      }
    }
  }
}

bool SignedIntegerOverflowChecker::runOnModule(Module& m) {
  DataLayout* dataLayout = new DataLayout(&m);
  Function* va = m.getFunction("__SMACK_overflow_false");
  //Function* co = m.getFunction("__SMACK_check_overflow");

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
            SmallVectorImpl<StringRef> *ar = new SmallVector<StringRef, 2>;
            if (f && f->hasName() && OVERFLOW_INTRINSICS.match(f->getName().str(), ar)) {
              std::string op = ar->back().str();
              unsigned int bits = 32;
              if (ei->getIndices()[0] == 0) {
                Value* o1 = ci->getArgOperand(0);
                Value* o2 = ci->getArgOperand(1);
                CastInst* so1 = CastInst::CreateSExtOrBitCast(o1, IntegerType::get(F.getContext(), bits*2), "", &*I);
                CastInst* so2 = CastInst::CreateSExtOrBitCast(o2, IntegerType::get(F.getContext(), bits*2), "", &*I);
                BinaryOperator* ai = BinaryOperator::Create(INSTRUCTION_TABLE.at(op), so1, so2, "", &*I);
                CastInst* tr = CastInst::CreateTruncOrBitCast(ai, IntegerType::get(F.getContext(), bits), "", &*I);
                replaceValue(&*I, tr);
                //I->eraseFromParent();
              }
              if (ei->getIndices()[0] == 1) {
                auto ai = std::prev(std::prev(std::prev(I)));
                ConstantInt* max = ConstantInt::get(IntegerType::get(F.getContext(), bits*2), "2147483647", 10);
                ConstantInt* min = ConstantInt::get(IntegerType::get(F.getContext(), bits*2), "-2147483648", 10);
                ICmpInst* gt = new ICmpInst(&*I, CmpInst::ICMP_SGT, &*ai, max, "");
                ICmpInst* lt = new ICmpInst(&*I, CmpInst::ICMP_SLT, &*ai, min, "");
                BinaryOperator* flag = BinaryOperator::Create(Instruction::Or, gt, lt, "", &*I);
                replaceValue(&*I, flag);
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
char SignedIntegerOverflowChecker::ID = 0;
}
