#include "smack/SplitStructLoadStore.h"
#include "llvm/IR/InstIterator.h"

namespace smack {

using namespace llvm;

bool SplitStructLoadStore::runOnModule(Module& M)
{
  DL = &M.getDataLayout();

  for (auto& F : M) {
    for(inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
      if (LoadInst* li = dyn_cast<LoadInst>(&*I)) {
        if (li->getType()->isAggregateType()) {
          //assert(isa<ReturnInst>(li->user_back()) && "General structure load not handled.");
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

void SplitStructLoadStore::splitStructStore(StoreInst* si, Value* ptr, Value* val)
{
  if (StructType* st = dyn_cast<StructType>(val->getType())) {
    std::vector<std::pair<Value*, unsigned> > idx;
    IRBuilder<> irb(si);
    copyStructs(&irb, ptr, st, val, idx);
    toRemove.push_back(si);
  }
  //assert(0 && "Store non-const values not supported.");
}

void SplitStructLoadStore::copyStructs(IRBuilder<> *irb, Value* ptr, Type* ct, Value* val, std::vector<std::pair<Value*, unsigned> > idxs)
{
  LLVMContext& C = ptr->getContext();
  Constant* cv = dyn_cast<Constant>(val);

  if (ct->isIntegerTy() || ct->isPointerTy() || ct->isFloatingPointTy()) {
    std::vector<Value*> vidxs;
    for (auto p = idxs.begin(); p != idxs.end(); ++p) {
      vidxs.push_back(std::get<0>(*p));
    }
    if (cv)
      irb->CreateStore(val, irb->CreateGEP(ptr, ArrayRef<Value*>(vidxs)));
    else {
      std::vector<unsigned> uidxs;
      for (auto p = idxs.begin()+1; p != idxs.end(); ++p) {
        uidxs.push_back(std::get<1>(*p));
      }
      irb->CreateStore(irb->CreateExtractValue(val, ArrayRef<unsigned>(uidxs)), irb->CreateGEP(ptr, ArrayRef<Value*>(vidxs)));
    }
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

