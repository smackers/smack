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
      } else if (ReturnInst *ri = dyn_cast<ReturnInst>(&I)) {
        Value *V = ri->getReturnValue();
        if (isConstantAggregate(V)) {
          visitAggregateValue(cast<Constant>(V), V->getType(), idx, info, C);
          splitConstantReturn(ri, info);
        }
      } else if (CallInst *ci = dyn_cast<CallInst>(&I)) {
        for (unsigned i = 0; i < ci->arg_size(); ++i) {
          Value *arg = ci->getArgOperand(i);
          if (isConstantAggregate(arg)) {
            info.clear();
            idx.clear();
            visitAggregateValue(cast<Constant>(arg), arg->getType(), idx, info,
                                C);
            splitConstantArg(ci, i, info);
          }
        }
      }
    }

    for (auto &i : toRemove)
      i->eraseFromParent();
  }
  return true;
}

bool SplitAggregateValue::isConstantAggregate(Value *V) {
  // we do not want to touch vector type here since there is
  // special support for it
  if (V && (V->getType()->isStructTy() || V->getType()->isArrayTy()))
    return isa<ConstantAggregate>(V) || isa<ConstantAggregateZero>(V);
  else
    return false;
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
    auto *load =
        irb.CreateLoad(cast<GEPOperator>(p)->getResultElementType(), p);
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
    Type *T = V->getType();
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

Value *SplitAggregateValue::createInsertedValue(IRBuilder<> &irb, Type *T,
                                                std::vector<InfoT> &info,
                                                Value *V) {
  Value *box = irb.CreateAlloca(T);
  splitAggregateStore(box, V, info, irb, false);
  return splitAggregateLoad(T, box, info, irb, false);
}

void SplitAggregateValue::splitConstantReturn(ReturnInst *ri,
                                              std::vector<InfoT> &info) {
  IRBuilder<> irb(ri);
  Type *T = ri->getReturnValue()->getType();
  ri->setOperand(0, createInsertedValue(irb, T, info, ri->getReturnValue()));
}

void SplitAggregateValue::splitConstantArg(CallInst *ci, unsigned i,
                                           std::vector<InfoT> &info) {
  IRBuilder<> irb(ci);
  Type *T = ci->getArgOperand(i)->getType();
  ci->setArgOperand(i, createInsertedValue(irb, T, info, ci->getArgOperand(i)));
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
    X("split-aggregate-values",
      "Split Load/Store/ConstantReturn of Aggregate Types");
} // namespace smack
