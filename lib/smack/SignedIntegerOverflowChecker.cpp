//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/SignedIntegerOverflowChecker.h"
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

namespace smack {

using namespace llvm;

Regex OVERFLOW_INTRINSICS("^llvm.s(add|sub|mul).with.overflow.i(32|64)$");

std::map<std::string, Instruction::BinaryOps> SignedIntegerOverflowChecker::INSTRUCTION_TABLE {
  {"add", Instruction::Add},
  {"sub", Instruction::Sub},
  {"mul", Instruction::Mul}
};

std::map<int, std::string> SignedIntegerOverflowChecker::INT_MAX_TABLE {
  {32, "2147483647"},
  {64, "9223372036854775807"}
};

std::map<int, std::string> SignedIntegerOverflowChecker::INT_MIN_TABLE {
  {32, "-2147483648"},
  {64, "-9223372036854775808"}
};

bool SignedIntegerOverflowChecker::runOnModule(Module& m) {
  Function* va = m.getFunction("__SMACK_overflow_false");
  Function* co = m.getFunction("__SMACK_check_overflow");

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
              std::string op = ar->begin()[1].str();
              std::string len = ar->begin()[2].str();
              int bits = std::stoi(len);
              if (ei->getIndices()[0] == 1) {
                Instruction* prev = &*std::prev(I);
                Value* o1 = ci->getArgOperand(0);
                Value* o2 = ci->getArgOperand(1);
                CastInst* so1 = CastInst::CreateSExtOrBitCast(o1, IntegerType::get(F.getContext(), bits*2), "", &*I);
                CastInst* so2 = CastInst::CreateSExtOrBitCast(o2, IntegerType::get(F.getContext(), bits*2), "", &*I);
                BinaryOperator* ai = BinaryOperator::Create(INSTRUCTION_TABLE.at(op), so1, so2, "", &*I);
                if (prev && isa<ExtractValueInst>(prev)) {
                  ExtractValueInst* pei = cast<ExtractValueInst>(prev);
                  if (auto pci = dyn_cast<CallInst>(pei->getAggregateOperand())) {
                    if (pci == ci) {
                      CastInst* tr = CastInst::CreateTruncOrBitCast(ai, IntegerType::get(F.getContext(), bits), "", &*I);
                      prev->replaceAllUsesWith(tr);
                    }
                  }
                }
                ConstantInt* max = ConstantInt::get(IntegerType::get(F.getContext(), bits*2), INT_MAX_TABLE.at(bits), 10);
                ConstantInt* min = ConstantInt::get(IntegerType::get(F.getContext(), bits*2), INT_MIN_TABLE.at(bits), 10);
                ICmpInst* gt = new ICmpInst(&*I, CmpInst::ICMP_SGT, ai, max, "");
                ICmpInst* lt = new ICmpInst(&*I, CmpInst::ICMP_SLT, ai, min, "");
                BinaryOperator* flag = BinaryOperator::Create(Instruction::Or, gt, lt, "", &*I);
                (*I).replaceAllUsesWith(flag);
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
            ConstantInt* max = ConstantInt::get(IntegerType::get(F.getContext(), bits*2), INT_MAX_TABLE.at(bits), 10);
            ConstantInt* min = ConstantInt::get(IntegerType::get(F.getContext(), bits*2), INT_MIN_TABLE.at(bits), 10);
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
  return true;
}

// Pass ID variable
char SignedIntegerOverflowChecker::ID = 0;
}
