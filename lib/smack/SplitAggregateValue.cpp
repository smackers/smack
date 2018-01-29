//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/SplitAggregateValue.h"
#include "llvm/IR/InstIterator.h"

namespace smack {

using namespace llvm;

std::vector<Value*> getFirsts(SplitAggregateValue::IndexT lst) {
  std::vector<Value*> ret;
  for (auto& p : lst)
    ret.push_back(std::get<0>(p));
  return ret;
}

std::vector<unsigned> getSeconds(SplitAggregateValue::IndexT lst) {
  std::vector<unsigned> ret;
  for (auto p = lst.begin()+1; p != lst.end(); ++p)
    ret.push_back(std::get<1>(*p));
  return ret;
}

bool SplitAggregateValue::runOnBasicBlock(BasicBlock& BB) {
  std::vector<Instruction*> toRemove;
  LLVMContext& C = BB.getContext();
  for(Instruction& I : BB) {
    IndexT idx;
    std::vector<InfoT> info;
    if (LoadInst* li = dyn_cast<LoadInst>(&I)) {
      if (li->getType()->isAggregateType()) {
        visitAggregateValue(nullptr, li->getType(), idx, info, C);
        splitAggregateLoad(li, info);
        toRemove.push_back(li);
      }
    } else if (StoreInst* si = dyn_cast<StoreInst>(&I)) {
      Value* V = si->getValueOperand();
      if (V->getType()->isAggregateType()) {
        visitAggregateValue(dyn_cast_or_null<Constant>(V), V->getType(), idx, info, C);
        splitAggregateStore(si, info);
        toRemove.push_back(si);
      }
    } else if (ReturnInst* ri = dyn_cast<ReturnInst>(&I)) {
      Value* V = ri->getReturnValue();
      if (auto crv = dyn_cast_or_null<ConstantAggregate>(V)) {
        visitAggregateValue(cast<Constant>(V), V->getType(), idx, info, C);
        splitConstantReturn(ri, info);
      }
    }
  }

  for (auto& i : toRemove)
    i->eraseFromParent();
  return true;
}

void SplitAggregateValue::splitAggregateLoad(LoadInst* li, std::vector<InfoT>& info) {
  IRBuilder<> irb(li);
  Value* V = UndefValue::get(li->getType());
  Value* P = li->getPointerOperand();
  for (auto& e : info) {
    IndexT idxs = std::get<0>(e);
    V = irb.CreateInsertValue(V,
      irb.CreateLoad(irb.CreateGEP(P, ArrayRef<Value*>(getFirsts(idxs)))),
      ArrayRef<unsigned>(getSeconds(idxs)));
  }
  li->replaceAllUsesWith(V);
}

void SplitAggregateValue::splitAggregateStore(StoreInst* si, std::vector<InfoT>& info) {
  IRBuilder<> irb(si);
  Value* P = si->getPointerOperand();
  Value* V = si->getValueOperand();
  for (auto& e : info) {
    IndexT idxs = std::get<0>(e);
    Constant* c = std::get<1>(e);
    std::vector<Value*> vidxs = getFirsts(idxs);
    if (c)
      irb.CreateStore(c, irb.CreateGEP(P, ArrayRef<Value*>(vidxs)));
    else
      irb.CreateStore(irb.CreateExtractValue(
        V, ArrayRef<unsigned>(getSeconds(idxs))),
          irb.CreateGEP(P, ArrayRef<Value*>(vidxs)));
  }
}

void SplitAggregateValue::splitConstantReturn(ReturnInst* ri, std::vector<InfoT>& info) {
  IRBuilder<> irb(ri);
  Type* T = ri->getReturnValue()->getType();
  Value* V = UndefValue::get(T);
  Value* box = irb.CreateAlloca(T);
  for (auto& e : info) {
    IndexT idxs = std::get<0>(e);
    Constant* c = std::get<1>(e);
    Value* P = irb.CreateGEP(box, ArrayRef<Value*>(getFirsts(idxs)));
    irb.CreateStore(c, P);
    V = irb.CreateInsertValue(V, irb.CreateLoad(P),
      ArrayRef<unsigned>(getSeconds(idxs)));
  }
  ri->setOperand(0, V);
}

void SplitAggregateValue::visitAggregateValue(Constant* baseVal, Type* T, IndexT idxs,
                                                    std::vector<InfoT>& info, LLVMContext& C){
  Constant* newBaseVal = baseVal;
  if(T->isIntegerTy() || T->isFloatingPointTy() || T->isPointerTy())
      info.push_back(std::make_pair(idxs, newBaseVal));
  else if (ArrayType* AT = dyn_cast<ArrayType>(T)) {
    for (unsigned i = 0; i < AT->getNumElements(); ++i) {
      newBaseVal = baseVal? baseVal->getAggregateElement(i) : baseVal;
      std::vector<std::pair<Value*, unsigned> > lidxs(idxs);
      if (lidxs.empty())
        lidxs.push_back(std::make_pair(ConstantInt::get(Type::getInt32Ty(C),0), 0));
      lidxs.push_back(std::make_pair(ConstantInt::get(Type::getInt64Ty(C),i), i));
      visitAggregateValue(newBaseVal, AT->getElementType(), lidxs, info, C);
    }
  } else if (StructType* ST = dyn_cast<StructType>(T)) {
    for (unsigned i = 0; i < ST->getNumElements(); ++i) {
      newBaseVal = baseVal? baseVal->getAggregateElement(i) : baseVal;
      std::vector<std::pair<Value*, unsigned> > lidxs(idxs);
      if (lidxs.empty())
        lidxs.push_back(std::make_pair(ConstantInt::get(Type::getInt32Ty(C),0), 0));
      lidxs.push_back(std::make_pair(ConstantInt::get(Type::getInt32Ty(C),i), i));
      visitAggregateValue(newBaseVal, ST->getElementType(i), lidxs, info, C);
    }
  } else
    llvm_unreachable("Unsupported type");
}

// Pass ID variable
char SplitAggregateValue::ID = 0;

// Register the pass
static RegisterPass<SplitAggregateValue>
X("split-aggregate-values", "Split Load/Store/ConstantReturn of Aggregate Types");

}

