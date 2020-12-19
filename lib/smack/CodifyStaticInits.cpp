//
// This file is distributed under the MIT License. See LICENSE for details.
//

#define DEBUG_TYPE "codify-static-inits"

#include "smack/CodifyStaticInits.h"
#include "smack/DSAWrapper.h"
#include "smack/Debug.h"
#include "smack/InitializePasses.h"
#include "smack/Naming.h"
#include "smack/SmackOptions.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/Regex.h"
#include "llvm/Support/raw_ostream.h"

#include <deque>
#include <queue>
#include <set>
#include <vector>

namespace smack {

using namespace llvm;

bool CodifyStaticInits::runOnModule(Module &M) {
  TD = &M.getDataLayout();
  LLVMContext &C = M.getContext();
  DSAWrapper *DSA = &getAnalysis<DSAWrapper>();

  Function *F = cast<Function>(
      M.getOrInsertFunction(Naming::STATIC_INIT_PROC, Type::getVoidTy(C))
          .getCallee());

  BasicBlock *B = BasicBlock::Create(C, "entry", F);
  IRBuilder<> IRB(B);

  std::deque<std::tuple<Constant *, Constant *, std::vector<Value *>>> worklist;

  for (auto &G : M.globals())
    if (G.hasInitializer() && DSA->isRead(&G))
      worklist.push_back(
          std::make_tuple(G.getInitializer(), &G, std::vector<Value *>()));

  while (worklist.size()) {
    Constant *V = std::get<0>(worklist.front());
    Constant *P = std::get<1>(worklist.front());
    std::vector<Value *> I = std::get<2>(worklist.front());
    worklist.pop_front();

    if (V->getType()->isIntegerTy() || V->getType()->isPointerTy() ||
        V->getType()->isFloatingPointTy() || V->getType()->isVectorTy())

      IRB.CreateStore(V, IRB.CreateGEP(P, ArrayRef<Value *>(I)));

    else if (ArrayType *AT = dyn_cast<ArrayType>(V->getType()))
      for (unsigned i = AT->getNumElements(); i-- > 0;) {
        auto A = V->getAggregateElement(i);
        std::vector<Value *> idxs(I);
        if (idxs.empty())
          idxs.push_back(ConstantInt::get(Type::getInt32Ty(C), 0));
        idxs.push_back(ConstantInt::get(Type::getInt64Ty(C), i));
        worklist.push_front(std::make_tuple(A, P, std::vector<Value *>(idxs)));
      }

    else if (StructType *ST = dyn_cast<StructType>(V->getType()))
      for (unsigned i = ST->getNumElements(); i-- > 0;) {
        auto A = V->getAggregateElement(i);
        std::vector<Value *> idxs(I);
        if (idxs.empty())
          idxs.push_back(ConstantInt::get(Type::getInt32Ty(C), 0));
        idxs.push_back(ConstantInt::get(Type::getInt32Ty(C), i));
        worklist.push_front(std::make_tuple(A, P, std::vector<Value *>(idxs)));
      }

    else
      assert(false && "Unexpected static initializer.");
  }

  IRB.CreateRetVoid();

  return true;
}

void CodifyStaticInits::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequired<DSAWrapper>();
}

Pass *createCodifyStaticInitsPass() { return new CodifyStaticInits(); }

} // namespace smack

char smack::CodifyStaticInits::ID = 0;

using namespace smack;
INITIALIZE_PASS_BEGIN(CodifyStaticInits, "codify-static-inits",
                      "Codify Static Initializers", false, false)
INITIALIZE_PASS_DEPENDENCY(DSAWrapper)
INITIALIZE_PASS_END(CodifyStaticInits, "codify-static-inits",
                    "Codify Static Initializers", false, false)
