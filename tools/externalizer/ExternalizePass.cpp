#include "ExternalizePass.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ValueMapper.h"

static llvm::cl::list<std::string>
    entryPoints("entry-points", llvm::cl::ZeroOrMore,
                llvm::cl::desc("Verification entry points"),
                llvm::cl::value_desc("PROCS"));

using namespace llvm;

namespace externalize {
// Based on internalizeFunctions
// from https://llvm.org/doxygen/Attributor_8cpp_source.html#l01948
Function *externalizeFunction(Function *Fn) {
  // Generate the externalized version of Fn
  Module &M = *Fn->getParent();
  FunctionType *FnTy = Fn->getFunctionType();

  // Create a copy of the current function
  Function *Copied =
      Function::Create(FnTy, GlobalValue::LinkageTypes::ExternalLinkage,
                       Fn->getAddressSpace(), Fn->getName() + ".externalized");
  ValueToValueMapTy VMap;
  auto *NewFArgIt = Copied->arg_begin();
  for (auto &Arg : Fn->args()) {
    auto ArgName = Arg.getName();
    NewFArgIt->setName(ArgName);
    VMap[&Arg] = &(*NewFArgIt++);
  }
  SmallVector<ReturnInst *, 8> Returns;

  // Copy the body of the original function to the new one
  CloneFunctionInto(Copied, Fn, VMap, false, Returns);

  // Copy metadata
  SmallVector<std::pair<unsigned, MDNode *>, 1> MDs;
  Fn->getAllMetadata(MDs);
  for (auto MDIt : MDs)
    if (!Copied->hasMetadata())
      Copied->addMetadata(MDIt.first, *MDIt.second);

  M.getFunctionList().insert(Fn->getIterator(), Copied);
  Copied->setDSOLocal(true);

  // Replace all uses of the old function with the new externalized function
  Fn->replaceAllUsesWith(Copied);

  return Copied;
}
bool ExternalizePass::runOnModule(Module &M) {
  bool changed = false;
  for (const std::string &e : entryPoints) {
    if (Function *f = M.getFunction(e)) {
      if (!f->hasExternalLinkage()) {
        changed = true;
        Function *external = externalizeFunction(f);
        f->removeFromParent();
        external->setName(e);
      }
    }
  }
  return changed;
}

char ExternalizePass::ID = 0;

StringRef ExternalizePass::getPassName() const {
  return "Externalize static entry point functions";
}
} // namespace externalize
