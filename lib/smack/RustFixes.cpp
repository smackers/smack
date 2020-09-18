//
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "smack/RustFixes.h"
#include "smack/Naming.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"
#include <string>
#include <set>

namespace smack {

using namespace llvm;

bool fixEntry(Function& main) {
  std::vector<Instruction *> instToErase;
  bool isRustEntry = false;
  for (inst_iterator I = inst_begin(main), E = inst_end(main); I != E; ++I) {
    if (auto ci = dyn_cast<CallInst>(&*I)) {
      if (Function *f = ci->getCalledFunction()) {
	std::string name = f->hasName() ? f->getName() : "";
	if (name.find(Naming::RUST_ENTRY) != std::string::npos) {
	  isRustEntry = true;
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
  
  for (auto I : instToErase) {
    I->eraseFromParent();
  }
  return isRustEntry;
}

void closeCalledFunctions(CallGraphNode *CGN, std::set<Function *> &callees) {
  if (!CGN) { return; }
  
  Function *function = CGN->getFunction();
  if (callees.count(function)) { return; }

  callees.insert(CGN->getFunction());
  for (auto cr : *CGN) {
    if (std::get<0>(cr)) {
      closeCalledFunctions(std::get<1>(cr), callees);
    }
  }
}

bool RustFixes::runOnModule(Module &m) {
  std::set<Function *> funcToErase;
  std::set<Function *> functions;
  Function *mainFunction = nullptr;
  bool isRust = false;
  
  for (auto &F : m) {
    if (F.hasName()) {
      auto name = F.getName();
      if (Naming::isSmackName(name))
	continue;
      functions.insert(&F);
      if (name == "main") {
	isRust |= fixEntry(F);
	mainFunction = &F;
      }
      else if (name.find("_ZN3std2rt19lang_start_internal") != std::string::npos ||
	       name.find(Naming::RUST_ENTRY) != std::string::npos) {
	funcToErase.insert(&F);
      }
    }
  }

  for (auto F : funcToErase) {
    F->dropAllReferences();
  }
  
  if (isRust) {
    CallGraph CG = CallGraph(m);
    auto mCFG = CG[mainFunction];
    std::set<Function *> callees;
    closeCalledFunctions(mCFG, callees);

    for (auto f : functions) {
      if (!callees.count(f)) {
	f->dropAllReferences();
      }
    }
  }
  return true;
}

// Pass ID variable
char RustFixes::ID = 0;

StringRef RustFixes::getPassName() const { return "Fixes for Rust programs"; }

} // namespace smack
