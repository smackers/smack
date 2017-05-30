//
// This file is distributed under the MIT License. See LICENSE for details.
//

#define DEBUG_TYPE "codify-static-inits"

#include "smack/CodifyStaticInits.h"
#include "smack/DSAWrapper.h"
#include "smack/Naming.h"
#include "smack/SmackOptions.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Regex.h"
#include "llvm/IR/DataLayout.h"

#include <deque>
#include <queue>
#include <set>
#include <vector>

namespace smack {

using namespace llvm;

namespace{
  Regex STRING_CONSTANT("^\\.str[.0-9]*$");

  bool isStringConstant(Value& V) {
    return STRING_CONSTANT.match(V.getName().str());
  }

  bool isBoogieCode(Value& V) {
    std::queue<Value*> worklist;
    std::set<Value*> covered;
    worklist.push(&V);
    covered.insert(&V);
    while (worklist.size()) {
      Value* U = worklist.front();
      worklist.pop();

      if (CallInst* CI = dyn_cast<CallInst>(U))
        if (Function* F = CI->getCalledFunction())
          if (F->hasName())
            if (F->getName().find(Naming::MOD_PROC) != std::string::npos
                || F->getName().find(Naming::CODE_PROC) != std::string::npos
                || F->getName().find(Naming::DECL_PROC) != std::string::npos
                || F->getName().find(Naming::TOP_DECL_PROC) != std::string::npos)
            return true;

      for (auto W : U->users())
        if (!covered.count(W)) {
          worklist.push(W);
          covered.insert(W);
        }
    }
    return false;
  }
}

bool CodifyStaticInits::runOnModule(Module& M) {
  TD = &M.getDataLayout();
  LLVMContext& C = M.getContext();
  DSAWrapper* DSA = &getAnalysis<DSAWrapper>();

  Function* F = dyn_cast<Function>(
    M.getOrInsertFunction(Naming::STATIC_INIT_PROC,
      Type::getVoidTy(C), NULL));

  BasicBlock* B = BasicBlock::Create(C, "entry", F);
  IRBuilder<> IRB(B);

  std::deque< std::tuple< Constant*, Constant*, std::vector<Value*> > > worklist;

  for (auto &G : M.globals())
    if (G.hasInitializer())

      // HACK: Normally only isRead should be necessary here. However, there
      // seems to be a bug in the DSA code which fails to mark some globals that
      // are read as read. Currently this has only been observed with globals
      // that have named addresses, e.g., excluding string constants. Thus the
      // second predicate here is a messy hack that has little to do with the
      // intended property of being read.
      if (DSA->isRead(&G) || !G.hasUnnamedAddr())

        worklist.push_back(std::make_tuple(
          G.getInitializer(), &G, std::vector<Value*>()));

  while (worklist.size()) {
    Constant* V = std::get<0>(worklist.front());
    Constant* P = std::get<1>(worklist.front());
    std::vector<Value*> I = std::get<2>(worklist.front());
    worklist.pop_front();

    if (V->getType()->isIntegerTy() ||
        V->getType()->isPointerTy() ||
        V->getType()->isFloatingPointTy())

      IRB.CreateStore(V, IRB.CreateGEP(P, ArrayRef<Value*>(I)));

    else if (ArrayType* AT = dyn_cast<ArrayType>(V->getType()))
      for (unsigned i = AT->getNumElements(); i-- > 0; ) {
        auto A = V->getAggregateElement(i);
        std::vector<Value*> idxs(I);
        if (idxs.empty())
          idxs.push_back(ConstantInt::get(Type::getInt32Ty(C),0));
        idxs.push_back(ConstantInt::get(Type::getInt64Ty(C),i));
        worklist.push_front(std::make_tuple(A, P, std::vector<Value*>(idxs)));
      }

    else if (StructType* ST = dyn_cast<StructType>(V->getType()))
      for (unsigned i = ST->getNumElements(); i-- > 0; ) {
        auto A = V->getAggregateElement(i);
        std::vector<Value*> idxs(I);
        if (idxs.empty())
          idxs.push_back(ConstantInt::get(Type::getInt32Ty(C),0));
        idxs.push_back(ConstantInt::get(Type::getInt32Ty(C),i));
        worklist.push_front(std::make_tuple(A, P, std::vector<Value*>(idxs)));
      }

    else if (V->getType()->isX86_FP80Ty())
      errs() << "warning: ignored X86 FP80 initializer" << "\n";

    else
      assert (false && "Unexpected static initializer.");
  }

  IRB.CreateRetVoid();

  return true;
}

void CodifyStaticInits::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequired<DSAWrapper>();
}

// Pass ID variable
char CodifyStaticInits::ID = 0;

// Register the pass
static RegisterPass<CodifyStaticInits>
X("codify-static-inits", "Codify Static Initializers");

}
