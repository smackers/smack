//
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "smack/RustFixes.h"
#include "smack/Naming.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Module.h"
#include <string>

namespace smack {

using namespace llvm;

bool RustFixes::runOnModule(Module &m) {
  std::vector<Instruction *> instToErase;
  for (auto &F : m) {
    if (F.hasName() && Naming::isSmackName(F.getName()))
      continue;
    for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
      if (auto ci = dyn_cast<CallInst>(&*I)) {
        if (Function *f = ci->getCalledFunction()) {
          std::string name = f->hasName() ? f->getName() : "";
          if (name.find(Naming::RUST_ENTRY) != std::string::npos) {
            // Get real Rust main
            auto castExpr = ci->getArgOperand(0);
            auto mainFunction = cast<Function>(castExpr);
            auto callMain = CallInst::Create(mainFunction->getFunctionType(),
                                             cast<Value>(mainFunction));

            // Replace lang_start call...
            auto retType = f->getReturnType();
            Constant *zero = ConstantInt::get(retType, 0);
            auto *result = BinaryOperator::Create(Instruction::Add, zero, zero);
            result->insertAfter(ci);
            callMain->insertAfter(result);
            I->replaceAllUsesWith(result);

            instToErase.push_back(&*I);
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
char RustFixes::ID = 0;

StringRef RustFixes::getPassName() const { return "Fixes for Rust programs"; }

} // namespace smack
