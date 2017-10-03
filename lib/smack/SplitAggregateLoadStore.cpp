//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/SplitAggregateLoadStore.h"
#include "llvm/IR/InstIterator.h"

namespace smack {

using namespace llvm;

std::vector<Value*> getFirsts(std::vector<std::pair<Value*, unsigned>> lst) {
  std::vector<Value*> ret;
  for (auto& p : lst)
    ret.push_back(std::get<0>(p));
  return ret;
}

std::vector<unsigned> getSeconds(std::vector<std::pair<Value*, unsigned>> lst) {
  std::vector<unsigned> ret;
  for (auto p = lst.begin()+1; p != lst.end(); ++p)
    ret.push_back(std::get<1>(*p));
  return ret;
}

static bool isUsedByReturnInst(Value* v) {
  for (auto u = v->user_begin(); u != v->user_end(); ++u) {
    if (isa<ReturnInst>(*u)) {
      return true;
    }
  }
  return false;
}

bool SplitAggregateLoadStore::runOnBasicBlock(BasicBlock& BB) {
  std::vector<Instruction*> toRemove;
  for(Instruction& I : BB) {
    if (LoadInst* li = dyn_cast<LoadInst>(&I)) {
      if (!isUsedByReturnInst(li) && li->getType()->isAggregateType()) {
        splitAggregateLoad(li);
        toRemove.push_back(li);
      }
    } else if (StoreInst* si = dyn_cast<StoreInst>(&I)) {
      Value* P = si->getPointerOperand();
      Value* V = si->getOperand(0)->stripPointerCasts();
      if (V->getType()->isAggregateType()) {
        splitAggregateStore(si, P, V);
        toRemove.push_back(si);
      }
    }
  }

  for (auto& i : toRemove)
    i->eraseFromParent();
  return true;
}

void SplitAggregateLoadStore::splitAggregateLoad(LoadInst* li) {
  std::vector<std::pair<Value*, unsigned>> idx;
  IRBuilder<> irb(li);
  li->replaceAllUsesWith(buildAggregateValues(&irb, li->getPointerOperand(), li->getType(), nullptr, idx));
}

Value* SplitAggregateLoadStore::buildAggregateValues(IRBuilder<> *irb, Value* ptr, Type* ct, Value* val,
                                            std::vector<std::pair<Value*, unsigned> > idxs) {
  LLVMContext& C = ptr->getContext();
  Value* cv = val? val : UndefValue::get(ct);

  if (ct->isIntegerTy() || ct->isPointerTy() || ct->isFloatingPointTy())
    return irb->CreateInsertValue(val,
             irb->CreateLoad(irb->CreateGEP(ptr, ArrayRef<Value*>(getFirsts(idxs)))),
               ArrayRef<unsigned>(getSeconds(idxs)));
  else if (ArrayType* AT = dyn_cast<ArrayType>(ct)) {
    for (unsigned i = 0; i < AT->getNumElements(); ++i) {
      std::vector<std::pair<Value*, unsigned> > lidxs(idxs);
      if (lidxs.empty())
        lidxs.push_back(std::make_pair(ConstantInt::get(Type::getInt32Ty(C),0), 0));
      lidxs.push_back(std::make_pair(ConstantInt::get(Type::getInt64Ty(C),i), i));
      cv = buildAggregateValues(irb, ptr, AT->getElementType(), cv, lidxs);
    }
  } else if (StructType* ST = dyn_cast<StructType>(ct)) {
    for (unsigned i = 0; i < ST->getNumElements(); ++i) {
      std::vector<std::pair<Value*, unsigned> > lidxs(idxs);
      if (lidxs.empty())
        lidxs.push_back(std::make_pair(ConstantInt::get(Type::getInt32Ty(C),0), 0));
      lidxs.push_back(std::make_pair(ConstantInt::get(Type::getInt32Ty(C),i), i));
      cv = buildAggregateValues(irb, ptr, ST->getElementType(i), cv, lidxs);
    }
  } else
    llvm_unreachable("Unsupported type");

  return cv;
}

void SplitAggregateLoadStore::splitAggregateStore(StoreInst* si, Value* ptr, Value* val) {
  std::vector<std::pair<Value*, unsigned>> idx;
  IRBuilder<> irb(si);
  copyAggregateValues(&irb, ptr, val->getType(), val, idx);
}

void SplitAggregateLoadStore::copyAggregateValues(IRBuilder<> *irb, Value* ptr, Type* ct, Value* val,
                                        std::vector<std::pair<Value*, unsigned> > idxs) {
  LLVMContext& C = ptr->getContext();
  Constant* cv = dyn_cast<Constant>(val);

  if (ct->isIntegerTy() || ct->isPointerTy() || ct->isFloatingPointTy()) {
    std::vector<Value*> vidxs = getFirsts(idxs);
    if (cv)
      irb->CreateStore(val, irb->CreateGEP(ptr, ArrayRef<Value*>(vidxs)));
    else
      irb->CreateStore(irb->CreateExtractValue(
        val, ArrayRef<unsigned>(getSeconds(idxs))),
          irb->CreateGEP(ptr, ArrayRef<Value*>(vidxs)));
  } else if (ArrayType* AT = dyn_cast<ArrayType>(ct)) {
    for (unsigned i = 0; i < AT->getNumElements(); ++i) {
      auto A = cv? cv->getAggregateElement(i) : val;
      std::vector<std::pair<Value*, unsigned> > lidxs(idxs);
      if (lidxs.empty())
        lidxs.push_back(std::make_pair(ConstantInt::get(Type::getInt32Ty(C),0), 0));
      lidxs.push_back(std::make_pair(ConstantInt::get(Type::getInt64Ty(C),i), i));
      copyAggregateValues(irb, ptr, AT->getElementType(), A, lidxs);
    }
  } else if (StructType* ST = dyn_cast<StructType>(ct)) {
    for (unsigned i = 0; i < ST->getNumElements(); ++i) {
      auto A = cv? cv->getAggregateElement(i) : val;
      std::vector<std::pair<Value*, unsigned> > lidxs(idxs);
      if (lidxs.empty())
        lidxs.push_back(std::make_pair(ConstantInt::get(Type::getInt32Ty(C),0), 0));
      lidxs.push_back(std::make_pair(ConstantInt::get(Type::getInt32Ty(C),i), i));
      copyAggregateValues(irb, ptr, ST->getElementType(i), A, lidxs);
    }
  } else
    llvm_unreachable("Unsupported type");
}

// Pass ID variable
char SplitAggregateLoadStore::ID = 0;

// Register the pass
static RegisterPass<SplitAggregateLoadStore>
X("split-aggregate-load-store", "Split Load/Store to Aggregate Types");

}

