//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/SplitAggregateValue.h"
#include "llvm/IR/InstIterator.h"

namespace smack {

using namespace llvm;

namespace SplitAggregateValueMetadata {
const char MemoryAccess[] = "split.aggregate.memory_access";
const char WholeMemoryAccess[] = "split.aggregate.whole_memory_access";
} // namespace SplitAggregateValueMetadata

namespace {
void markSplitAggregateAccess(Instruction *I, bool checkWholeAccess) {
  auto &C = I->getContext();
  auto *Marker =
      MDNode::get(C, ConstantAsMetadata::get(ConstantInt::getTrue(C)));
  I->setMetadata(SplitAggregateValueMetadata::MemoryAccess, Marker);
  if (checkWholeAccess)
    I->setMetadata(SplitAggregateValueMetadata::WholeMemoryAccess, Marker);
}
} // namespace

std::vector<Value *> getFirsts(SplitAggregateValue::IndexT lst) {
  std::vector<Value *> ret;
  for (auto &p : lst)
    ret.push_back(std::get<0>(p));
  return ret;
}

std::vector<unsigned> getSeconds(SplitAggregateValue::IndexT lst) {
  std::vector<unsigned> ret;
  for (auto p = lst.begin() + 1; p != lst.end(); ++p)
    ret.push_back(std::get<1>(*p));
  return ret;
}

bool SplitAggregateValue::runOnFunction(Function &F) {
  for (auto &BB : F) {
    std::vector<Instruction *> toRemove;
    LLVMContext &C = BB.getContext();
    for (Instruction &I : BB) {
      IndexT idx;
      std::vector<InfoT> info;
      if (LoadInst *li = dyn_cast<LoadInst>(&I)) {
        if (li->getType()->isAggregateType()) {
          visitAggregateValue(nullptr, li->getType(), idx, info, C);
          IRBuilder<> irb(li);
          li->replaceAllUsesWith(splitAggregateLoad(
              li->getType(), li->getPointerOperand(), info, irb, true));
          toRemove.push_back(li);
        }
      } else if (StoreInst *si = dyn_cast<StoreInst>(&I)) {
        Value *V = si->getValueOperand();
        if (V->getType()->isAggregateType()) {
          visitAggregateValue(dyn_cast_or_null<Constant>(V), V->getType(), idx,
                              info, C);
          IRBuilder<> irb(si);
          splitAggregateStore(si->getPointerOperand(), si->getValueOperand(),
                              info, irb, true);
          toRemove.push_back(si);
        }
      }
    }

    for (auto &i : toRemove)
      i->eraseFromParent();
  }
  return true;
}

Value *SplitAggregateValue::splitAggregateLoad(Type *T, Value *P,
                                               std::vector<InfoT> &info,
                                               IRBuilder<> &irb,
                                               bool preserveWholeAccessCheck) {
  Value *V = UndefValue::get(T);
  bool checkWholeAccess = preserveWholeAccessCheck;
  for (auto &e : info) {
    IndexT idxs = std::get<0>(e);
    Value *p = irb.CreateGEP(T, P, ArrayRef<Value *>(getFirsts(idxs)));
    auto *load = irb.CreateLoad(
        p->getType()->getScalarType()->getPointerElementType(), p);
    markSplitAggregateAccess(load, checkWholeAccess);
    checkWholeAccess = false;
    V = irb.CreateInsertValue(V, load, ArrayRef<unsigned>(getSeconds(idxs)));
  }
  return V;
}

void SplitAggregateValue::splitAggregateStore(Value *P, Value *V,
                                              std::vector<InfoT> &info,
                                              IRBuilder<> &irb,
                                              bool preserveWholeAccessCheck) {
  bool checkWholeAccess = preserveWholeAccessCheck;
  for (auto &e : info) {
    IndexT idxs = std::get<0>(e);
    Constant *c = std::get<1>(e);
    std::vector<Value *> vidxs = getFirsts(idxs);
    Type *T = P->getType()->getScalarType()->getPointerElementType();
    Value *p = irb.CreateGEP(T, P, ArrayRef<Value *>(vidxs));
    StoreInst *store;
    if (c)
      store = irb.CreateStore(c, p);
    else
      store = irb.CreateStore(
          irb.CreateExtractValue(V, ArrayRef<unsigned>(getSeconds(idxs))), p);
    markSplitAggregateAccess(store, checkWholeAccess);
    checkWholeAccess = false;
  }
}

void SplitAggregateValue::visitAggregateValue(Constant *baseVal, Type *T,
                                              IndexT idxs,
                                              std::vector<InfoT> &info,
                                              LLVMContext &C) {
  Constant *newBaseVal = baseVal;
  if (T->isIntegerTy() || T->isFloatingPointTy() || T->isPointerTy())
    info.push_back({idxs, newBaseVal});
  else if (ArrayType *AT = dyn_cast<ArrayType>(T)) {
    for (unsigned i = 0; i < AT->getNumElements(); ++i) {
      newBaseVal = baseVal ? baseVal->getAggregateElement(i) : baseVal;
      IndexT lidxs(idxs);
      if (lidxs.empty())
        lidxs.push_back({ConstantInt::get(Type::getInt32Ty(C), 0), 0});
      lidxs.push_back({ConstantInt::get(Type::getInt64Ty(C), i), i});
      visitAggregateValue(newBaseVal, AT->getElementType(), lidxs, info, C);
    }
  } else if (StructType *ST = dyn_cast<StructType>(T)) {
    for (unsigned i = 0; i < ST->getNumElements(); ++i) {
      newBaseVal = baseVal ? baseVal->getAggregateElement(i) : baseVal;
      IndexT lidxs(idxs);
      if (lidxs.empty())
        lidxs.push_back({ConstantInt::get(Type::getInt32Ty(C), 0), 0});
      lidxs.push_back({ConstantInt::get(Type::getInt32Ty(C), i), i});
      visitAggregateValue(newBaseVal, ST->getElementType(i), lidxs, info, C);
    }
  } else
    llvm_unreachable("Unsupported type");
}

// Pass ID variable
char SplitAggregateValue::ID = 0;

// Register the pass
static RegisterPass<SplitAggregateValue>
    X("split-aggregate-values", "Split Load/Store of Aggregate Types");
} // namespace smack
