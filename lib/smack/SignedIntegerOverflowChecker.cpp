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
#include <vector>

namespace smack {

using namespace llvm;

bool SignedIntegerOverflowChecker::runOnModule(Module& m) {
  DataLayout* dataLayout = new DataLayout(&m);
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
            if (ci->getCalledFunction()->getName().str() == "llvm.sadd.with.overflow.i32") {
              if (ei->getIndices()[0] == 0) {
                // create add instruction and link it to the next user
                Value* o1 = ci->getArgOperand(0);
                Value* o2 = ci->getArgOperand(1);
                BinaryOperator* ai = BinaryOperator::Create(Instruction::Add, o1, o2,"", &*I);
                for (auto u : ei->users()) {
                  if (auto i = dyn_cast<Instruction>(u)) {
                    if (i != &*I) {
                      for (unsigned c = 0; c < i->getNumOperands(); ++c) {
                        if (i->getOperand(c) == &*I)
                          i->setOperand(c, ai);
                      }
                    }
                  }
                }
                //I->removeFromParent();
              }
              if (ei->getIndices()[0] == 1) {
                auto ai = std::prev(std::prev(I));
                CallInst* flag = CallInst::Create(co, {&*ai}, "", &*I);
                for (auto u : ei->users()) {
                  if (auto i = dyn_cast<Instruction>(u)) {
                    if (i != &*I) {
                      for (unsigned c = 0; c < i->getNumOperands(); ++c) {
                        if (i->getOperand(c) == &*I)
                          i->setOperand(c, flag);
                      }
                    }
                  }
                }
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
