#include "smack/SplitStructLoadStore.h"
#include "llvm/IR/InstIterator.h"

namespace smack {

using namespace llvm;

std::vector<Value*> getFirsts(std::vector<std::pair<Value*, unsigned> > lst)
{
    std::vector<Value*> ret;
    for (auto p = lst.begin(); p != lst.end(); ++p)
      ret.push_back(std::get<0>(*p));
    return ret;
}

std::vector<unsigned> getSeconds(std::vector<std::pair<Value*, unsigned> > lst)
{
    std::vector<unsigned> ret;
    for (auto p = lst.begin()+1; p != lst.end(); ++p)
      ret.push_back(std::get<1>(*p));
    return ret;
}

bool SplitStructLoadStore::runOnModule(Module& M)
{
  DL = &M.getDataLayout();

  for (auto& F : M) {
    for(inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
      if (LoadInst* li = dyn_cast<LoadInst>(&*I)) {
        bool isReturnValue = false;
        for (auto u = li->user_begin(); u != li->user_end(); ++u)
        {
          if (auto ri = dyn_cast<ReturnInst>(*u)) {
            isReturnValue = true;
            break;
          }
        }
        if (!isReturnValue && li->getType()->isAggregateType()) {
          splitStructLoad(li);
        }
      } else if (StoreInst* si = dyn_cast<StoreInst>(&*I)) {
        Value* P = si->getPointerOperand();
        Value* V = si->getOperand(0)->stripPointerCasts();
        if (V->getType()->isAggregateType()) {
          splitStructStore(si, P, V);
        }
      }
    }
  }

  for (auto& i : toRemove)
    i->eraseFromParent();
  return true;
}

void SplitStructLoadStore::splitStructLoad(LoadInst* li)
{
  if (StructType* st = dyn_cast<StructType>(li->getType())) {
    std::vector<std::pair<Value*, unsigned> > idx;
    IRBuilder<> irb(li);
    li->replaceAllUsesWith(buildStructs(&irb, li->getPointerOperand(), st, nullptr, idx));
    toRemove.push_back(li);
  }
}

Value* SplitStructLoadStore::buildStructs(IRBuilder<> *irb, Value* ptr, Type* ct, Value* val, std::vector<std::pair<Value*, unsigned> > idxs)
{
  LLVMContext& C = ptr->getContext();
  Value* cv = val? val : UndefValue::get(ct);

  if (ct->isIntegerTy() || ct->isPointerTy() || ct->isFloatingPointTy())
    return irb->CreateInsertValue(val,
             irb->CreateLoad(irb->CreateGEP(ptr, ArrayRef<Value*>(getFirsts(idxs)))),
               ArrayRef<unsigned>(getSeconds(idxs)));
  else if (ArrayType* AT = dyn_cast<ArrayType>(ct)) {
    for (unsigned i = AT->getNumElements(); i-- > 0; ) {
      std::vector<std::pair<Value*, unsigned> > lidxs(idxs);
      if (lidxs.empty())
        lidxs.push_back(std::make_pair(ConstantInt::get(Type::getInt32Ty(C),0), 0));
      lidxs.push_back(std::make_pair(ConstantInt::get(Type::getInt64Ty(C),i), i));
      cv = buildStructs(irb, ptr, AT->getElementType(), cv, lidxs);
    }
  }
  else if (StructType* ST = dyn_cast<StructType>(ct)) {
    for (unsigned i = ST->getNumElements(); i-- > 0; ) {
      std::vector<std::pair<Value*, unsigned> > lidxs(idxs);
      if (lidxs.empty())
        lidxs.push_back(std::make_pair(ConstantInt::get(Type::getInt32Ty(C),0), 0));
      lidxs.push_back(std::make_pair(ConstantInt::get(Type::getInt32Ty(C),i), i));
      cv = buildStructs(irb, ptr, ST->getElementType(i), cv, lidxs);
    }
  }

  return cv;
}

void SplitStructLoadStore::splitStructStore(StoreInst* si, Value* ptr, Value* val)
{
  if (StructType* st = dyn_cast<StructType>(val->getType())) {
    std::vector<std::pair<Value*, unsigned> > idx;
    IRBuilder<> irb(si);
    copyStructs(&irb, ptr, st, val, idx);
    toRemove.push_back(si);
  }
}

void SplitStructLoadStore::copyStructs(IRBuilder<> *irb, Value* ptr, Type* ct, Value* val, std::vector<std::pair<Value*, unsigned> > idxs)
{
  LLVMContext& C = ptr->getContext();
  Constant* cv = dyn_cast<Constant>(val);

  if (ct->isIntegerTy() || ct->isPointerTy() || ct->isFloatingPointTy()) {
    std::vector<Value*> vidxs = getFirsts(idxs);
    if (cv)
      irb->CreateStore(val, irb->CreateGEP(ptr, ArrayRef<Value*>(vidxs)));
    else
      irb->CreateStore(
        irb->CreateExtractValue(val, ArrayRef<unsigned>(getSeconds(idxs))),
          irb->CreateGEP(ptr, ArrayRef<Value*>(vidxs)));
  }
  else if (ArrayType* AT = dyn_cast<ArrayType>(ct)) {
    for (unsigned i = AT->getNumElements(); i-- > 0; ) {
      auto A = cv? cv->getAggregateElement(i) : val;
      std::vector<std::pair<Value*, unsigned> > lidxs(idxs);
      if (lidxs.empty())
        lidxs.push_back(std::make_pair(ConstantInt::get(Type::getInt32Ty(C),0), 0));
      lidxs.push_back(std::make_pair(ConstantInt::get(Type::getInt64Ty(C),i), i));
      copyStructs(irb, ptr, AT->getElementType(), A, lidxs);
    }
  }
  else if (StructType* ST = dyn_cast<StructType>(ct)) {
    for (unsigned i = ST->getNumElements(); i-- > 0; ) {
      auto A = cv? cv->getAggregateElement(i) : val;
      std::vector<std::pair<Value*, unsigned> > lidxs(idxs);
      if (lidxs.empty())
        lidxs.push_back(std::make_pair(ConstantInt::get(Type::getInt32Ty(C),0), 0));
      lidxs.push_back(std::make_pair(ConstantInt::get(Type::getInt32Ty(C),i), i));
      copyStructs(irb, ptr, ST->getElementType(i), A, lidxs);
    }
  }
}
// Pass ID variable
char SplitStructLoadStore::ID = 0;

// Register the pass
static RegisterPass<SplitStructLoadStore>
X("split-struct-load-store", "Split Load/Store to Structures");

}

