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
    if (ConstantStruct* cs = dyn_cast<ConstantStruct>(val)) {
      std::vector<Value*> idx;
      IRBuilder<> irb(si);
      copyStructs(&irb, ptr, cs, idx);
      toRemove.push_back(si);
    }
  }
  //assert(0 && "Store non-const values not supported.");
}

void SplitStructLoadStore::copyStructs(IRBuilder<> *irb, Value* ptr, Constant* val, std::vector<Value*> idxs)
{
  LLVMContext& C = ptr->getContext();

  if (val->getType()->isIntegerTy() ||
      val->getType()->isPointerTy() ||
      val->getType()->isFloatingPointTy())
    irb->CreateStore(val, irb->CreateGEP(ptr, ArrayRef<Value*>(idxs)));
  else if (ArrayType* AT = dyn_cast<ArrayType>(val->getType())) {
    for (unsigned i = AT->getNumElements(); i-- > 0; ) {
      auto A = val->getAggregateElement(i);
      std::vector<Value*> lidxs(idxs);
      if (lidxs.empty())
        lidxs.push_back(ConstantInt::get(Type::getInt32Ty(C),0));
      lidxs.push_back(ConstantInt::get(Type::getInt64Ty(C),i));
      copyStructs(irb, ptr, A, lidxs);
    }
  }
  else if (StructType* ST = dyn_cast<StructType>(val->getType())) {
    for (unsigned i = ST->getNumElements(); i-- > 0; ) {
      auto A = val->getAggregateElement(i);
      std::vector<Value*> lidxs(idxs);
      if (lidxs.empty())
        lidxs.push_back(ConstantInt::get(Type::getInt32Ty(C),0));
      lidxs.push_back(ConstantInt::get(Type::getInt32Ty(C),i));
      copyStructs(irb, ptr, A, lidxs);
    }
  }
}
// Pass ID variable
char SplitStructLoadStore::ID = 0;

// Register the pass
static RegisterPass<SplitStructLoadStore>
X("split-struct-load-store", "Split Load/Store to Structures");

}
