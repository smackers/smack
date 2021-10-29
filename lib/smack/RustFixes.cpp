//
// This file is distributed under the MIT License. See LICENSE for details.
//
// This patches Rust programs by removing certain language specific functions,
// enabling later optimizations.
//

#include "smack/RustFixes.h"
#include "smack/Naming.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"
#include <map>
#include <string>

namespace smack {

using namespace llvm;

bool isRustNameMatch(StringRef search, StringRef name) {
  // Check if we are looking for a Rust mangled name with a 17 character hash
  // suffix, denoted by `17h'
  bool hashed_match = search.endswith("17h") && name.startswith(search) &&
                      search.size() + 17 == name.size();
  bool exact_match = search == name;
  return hashed_match || exact_match;
}

bool replaceSpecialRustFunctions(Function &f) {
  std::vector<Instruction *> to_remove;

  bool changed = false;
  static const std::map<StringRef, StringRef> alloc_fns = {
      {"_ZN5alloc5alloc5alloc17h", "__smack_rust_std_alloc"},
      {"_ZN5alloc5alloc12alloc_zeroed17h", "__smack_rust_std_alloc_zeroed"},
      {"_ZN5alloc5alloc7dealloc17h", "__smack_rust_std_dealloc"},
      {"_ZN5alloc5alloc7realloc17h", "__smack_rust_std_realloc"},
      {"__rust_alloc", "__smack_rust_prim_alloc"},
      {"__rust_alloc_zeroed", "__smack_rust_prim_alloc_zeroed"},
      {"__rust_dealloc", "__smack_rust_prim_dealloc"},
      {"__rust_realloc", "__smack_rust_prim_realloc"},
  };

  for (inst_iterator I = inst_begin(f), E = inst_end(f); I != E; ++I) {
    if (auto ci = dyn_cast<CallInst>(&*I)) {
      if (Function *f = ci->getCalledFunction()) {
        auto name = f->hasName() ? f->getName() : "";
        for (auto &kv : alloc_fns) {
          if (isRustNameMatch(std::get<0>(kv), name)) {
            Function *replacement =
                f->getParent()->getFunction(std::get<1>(kv));
            assert(replacement != NULL && "Function should be present.");
            changed = true;
            ci->setCalledFunction(replacement);
          }
        }

        if (Naming::isRustPanic(name)) {
          // Remove the calls rust panic functions
          changed = true;
          // Keep track of the panic call
          Module *m = f->getParent();
          FunctionCallee marker = m->getOrInsertFunction(
              Naming::RUST_PANIC_MARKER, Type::getVoidTy(m->getContext()));
          CallInst *panic_marker = CallInst::Create(marker);
          panic_marker->setDebugLoc(ci->getDebugLoc());
          panic_marker->insertBefore(ci);
          to_remove.push_back(ci);
        }
      }
    }
  }

  for (auto ci : to_remove) {
    ci->eraseFromParent();
  }

  return changed;
}

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

Returns true if this is a Rust program entry point, false
otherwise.
*/
bool fixEntry(Function &main) {
  std::vector<Instruction *> instToErase;

  for (inst_iterator I = inst_begin(main), E = inst_end(main); I != E; ++I) {
    if (auto ci = dyn_cast<CallInst>(&*I)) {
      if (Function *f = ci->getCalledFunction()) {
        StringRef name = f->hasName() ? f->getName() : "";
        if (name.find(Naming::RUST_ENTRY) != StringRef::npos) {
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

  return instToErase.size();
}

bool RustFixes::runOnFunction(Function &F) {
  bool result = false;
  if (F.hasName()) {
    StringRef name = F.getName();
    if (Naming::isSmackName(name)) {
      return false;
    } else if (name.find(Naming::RUST_LANG_START_INTERNAL) != StringRef::npos ||
               name.find(Naming::RUST_ENTRY) != StringRef::npos ||
               Naming::isRustPanic(name)) {
      F.dropAllReferences();
      return true;
    }

    if (name == "main") {
      result |= fixEntry(F);
    }
    result |= replaceSpecialRustFunctions(F);
  }

  return result;
}

// Pass ID variable
char RustFixes::ID = 0;

StringRef RustFixes::getPassName() const { return "Fixes for Rust programs"; }

} // namespace smack
