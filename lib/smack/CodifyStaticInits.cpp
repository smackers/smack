//
// This file is distributed under the MIT License. See LICENSE for details.
//

#define DEBUG_TYPE "codify-static-inits"

#include "smack/CodifyStaticInits.h"
#include "smack/DSAWrapper.h"
#include "smack/Debug.h"
#include "smack/InitializePasses.h"
#include "smack/LlvmCompat.h"
#include "smack/Naming.h"
#include "smack/SmackOptions.h"
#include "llvm/Config/llvm-config.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/Alignment.h"
#include "llvm/Support/Regex.h"
#include "llvm/Support/raw_ostream.h"

#include <deque>
#include <functional>
#include <queue>
#include <set>
#include <vector>

#include "smack/DSAWrapperAnalysis.h"

namespace smack {

using namespace llvm;

bool CodifyStaticInits::runOnModule(Module &M) {
  return runImpl(M, getAnalysis<DSAWrapper>());
}

bool CodifyStaticInits::runImpl(Module &M, DSAWrapper &dsaRef) {
  const DataLayout *TD = &M.getDataLayout();
  LLVMContext &C = M.getContext();
  DSAWrapper *DSA = &dsaRef;

  Function *F = cast<Function>(
      M.getOrInsertFunction(Naming::STATIC_INIT_PROC, Type::getVoidTy(C))
          .getCallee());

  BasicBlock *B = BasicBlock::Create(C, "entry", F);
  IRBuilder<> IRB(B);

  std::deque<std::tuple<Constant *, Constant *, std::vector<Value *>>> worklist;
  std::set<GlobalVariable *> queuedGlobals;

  std::function<bool(Type *)> isByteZeroSafeType = [&](Type *T) -> bool {
    if (T->isIntegerTy())
      return true;
    if (auto *AT = dyn_cast<ArrayType>(T))
      return isByteZeroSafeType(AT->getElementType());
    if (auto *ST = dyn_cast<StructType>(T)) {
      for (Type *ElementT : ST->elements())
        if (!isByteZeroSafeType(ElementT))
          return false;
      return true;
    }
    return false;
  };

  auto emitLargeZeroMemset = [&](GlobalVariable *G) -> bool {
    unsigned threshold = SmackOptions::StaticInitZeroMemsetThreshold;
    if (threshold == 0 || !G->hasInitializer())
      return false;

    Constant *Init = G->getInitializer();
    Type *T = G->getValueType();
    if (!Init->isNullValue() || !T->isSized() || !isByteZeroSafeType(T))
      return false;

    uint64_t byteSize = fixedTypeAllocSize(*TD, T);
    if (byteSize < threshold)
      return false;

    Value *Dst = G;
#if LLVM_VERSION_MAJOR < 15
    Dst = IRB.CreateBitCast(G, Type::getInt8PtrTy(C));
#endif
    IRB.CreateMemSet(Dst, ConstantInt::get(Type::getInt8Ty(C), 0),
                     ConstantInt::get(Type::getInt64Ty(C), byteSize),
                     MaybeAlign(1), false);
    return true;
  };

  auto enqueueGlobal = [&](GlobalVariable *G) {
    if (G->hasInitializer() && queuedGlobals.insert(G).second) {
      if (emitLargeZeroMemset(G))
        return;
      worklist.push_back(
          std::make_tuple(G->getInitializer(), G, std::vector<Value *>()));
    }
  };

  std::function<void(Constant *)> enqueueReferencedGlobals =
      [&](Constant *Cst) {
        if (auto *GV = dyn_cast<GlobalVariable>(Cst->stripPointerCasts())) {
          enqueueGlobal(GV);
          return;
        }

        for (Value *Op : Cst->operands())
          if (auto *OpC = dyn_cast<Constant>(Op))
            enqueueReferencedGlobals(OpC);
      };

  for (auto &G : M.globals())
    if (G.hasInitializer() && DSA->isRead(&G))
      enqueueGlobal(&G);

  while (worklist.size()) {
    Constant *V = std::get<0>(worklist.front());
    Constant *P = std::get<1>(worklist.front());
    std::vector<Value *> I = std::get<2>(worklist.front());
    worklist.pop_front();

    enqueueReferencedGlobals(V);

    if (V->getType()->isIntegerTy() || V->getType()->isPointerTy() ||
        V->getType()->isFloatingPointTy() || V->getType()->isVectorTy()) {
      Type *T = nullptr;
      if (auto *G = dyn_cast<GlobalVariable>(P))
        T = G->getValueType();
      else
        T = legacyPointerElementType(P);
      assert(T && "Expected static initializer pointer element type.");
      IRB.CreateStore(V, IRB.CreateGEP(T, P, ArrayRef<Value *>(I)));
    } else if (ArrayType *AT = dyn_cast<ArrayType>(V->getType()))
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

llvm::PreservedAnalyses
CodifyStaticInitsNewPM::run(Module &M, llvm::ModuleAnalysisManager &MAM) {
  auto &dsa = MAM.getResult<DSAWrapperAnalysis>(M);
  bool changed = CodifyStaticInits::runImpl(M, *dsa.wrapper);
  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

} // namespace smack

char smack::CodifyStaticInits::ID = 0;

using namespace smack;
INITIALIZE_PASS_BEGIN(CodifyStaticInits, "codify-static-inits",
                      "Codify Static Initializers", false, false)
INITIALIZE_PASS_DEPENDENCY(DSAWrapper)
INITIALIZE_PASS_END(CodifyStaticInits, "codify-static-inits",
                    "Codify Static Initializers", false, false)
