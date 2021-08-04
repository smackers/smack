//
// This file is distributed under the MIT License. See LICENSE for details.
//

//
// This pass adds:
//   1) A dummy main function, which calls the entry points for the program.
//   2) A dummy function which calls internally linked entry points.
//

#include <string>

#include "smack/InsertDummyMain.h"
#include "smack/Debug.h"
#include "smack/SmackOptions.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"

namespace smack {

using namespace llvm;

DenseMap<const Type*, FunctionCallee> m_ndfn;

FunctionCallee makeDummyFn(Module &m, Type *type, size_t num, std::string base) {
  std::string name = base + std::to_string(num);

  while(m.getNamedValue(name)) {
    name = base + std::to_string(num);
    num++;
  }

  return m.getOrInsertFunction(name, type);
}
  
FunctionCallee getNondetFn(Type *type, Module& M) {
  FunctionCallee res = m_ndfn[type];
  if (!res) {
    res = makeDummyFn(M, type, m_ndfn.size(), "__smack_arg_dummy_");
    m_ndfn[type] = res;
  }
  return res;
}

  
void insertEntryPointCaller(StringRef name,
			    const llvm::cl::list<std::string>& entries,
                            Module &m) {
  LLVMContext &ctx = m.getContext ();
  Type *intTy = Type::getInt32Ty (ctx);

  ArrayRef<Type*> params;
  Function *dummy = Function::Create (FunctionType::get(intTy, params, false),
				      GlobalValue::LinkageTypes::ExternalLinkage,
				      name, &m);


  IRBuilder<> B (ctx);
  BasicBlock *BB = BasicBlock::Create(ctx, "", dummy);
  B.SetInsertPoint(BB, BB->begin());

  for (auto entry : entries) {
    Function *F = m.getFunction(entry);

    if (!F) {
      for (const Function &l : m.getFunctionList()) {
	if (l.hasName()) errs() << l.getName() << "\n";
      }
      errs() << entry << " not found!\n";
      continue;
    }

    // Call F with dummy parameters
    SmallVector<Value*, 16> args;
    for (auto &arg : F->args()) {
      FunctionCallee ndf = getNondetFn(arg.getType(), m);
      args.push_back(B.CreateCall(ndf));
    }
    CallInst *CI = B.CreateCall(F, args);
  }

  B.CreateRet(ConstantInt::get(intTy, 0));
  errs() << *dummy << "\n";
}

bool InsertDummyMain::runOnModule(Module &m) {
  bool modified = false;

  if (!m.getFunction("main")) {
    insertEntryPointCaller("main", SmackOptions::EntryPoints, m);
    modified = true;
  }

  return modified;
}

// Pass ID variable
char InsertDummyMain::ID = 0;

StringRef InsertDummyMain::getPassName() const {
  return "Add dummy functions to call entry points";
}
} // namespace smack
