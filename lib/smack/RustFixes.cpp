//
// This file is distributed under the MIT License. See LICENSE for details.
//
// This patches Rust programs by removing certain language specific functions,
// enabling later optimizations.
//

#include "smack/RustFixes.h"
#include "smack/Naming.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"
#include <set>
#include <string>

namespace smack {

using namespace llvm;

/*
The main function of rust programs looks like this:
...
%r = call i32 @std::rt::lang_start(..., @real_main, ...)
...

This patches the main function to:
...
%r = 0
call void @real_main(...)
...
*/
void fixEntry(Function &main) {
  std::vector<Instruction *> instToErase;

  for (inst_iterator I = inst_begin(main), E = inst_end(main); I != E; ++I) {
    if (auto ci = dyn_cast<CallInst>(&*I)) {
      if (Function *f = ci->getCalledFunction()) {
        std::string name = f->hasName() ? f->getName() : "";
        if (name.find(Naming::RUST_ENTRY) != std::string::npos) {
          // Get real Rust main
          auto castExpr = ci->getArgOperand(0);
          auto mainFunction = cast<Function>(castExpr);
          auto callMain = CallInst::Create(mainFunction->getFunctionType(),
                                           cast<Value>(mainFunction));

          // Replace the call to lang_start with the real Rust main function
          auto retType = f->getReturnType();
          // Create a fake return value for this instruction
          Constant *zero = ConstantInt::get(retType, 0);
          auto *result = BinaryOperator::Create(Instruction::Add, zero, zero);
          result->insertAfter(ci);
          // Call the real main function
          callMain->insertAfter(result);
          I->replaceAllUsesWith(result);

          instToErase.push_back(&*I);
        }
      }
    }
  }

  for (auto I : instToErase) {
    I->eraseFromParent();
  }
}

bool RustFixes::runOnModule(Module &m) {
  std::set<Function *> funcToErase;

  for (auto &F : m) {
    if (F.hasName()) {
      auto name = F.getName();
      if (Naming::isSmackName(name))
        continue;
      if (name == "main") {
        fixEntry(F);
      } else if (name.find(Naming::RUST_LANG_START_INTERNAL) !=
                     std::string::npos ||
                 name.find(Naming::RUST_ENTRY) != std::string::npos) {
        funcToErase.insert(&F);
      }
    }
  }

  for (auto F : funcToErase) {
    F->dropAllReferences();
  }

  return true;
}

// Pass ID variable
char RustFixes::ID = 0;

StringRef RustFixes::getPassName() const { return "Fixes for Rust programs"; }

} // namespace smack
