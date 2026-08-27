//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/LowerVarArgs.h"
#include "smack/Debug.h"
#include "smack/Naming.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Support/MathExtras.h"
#include "llvm/Transforms/Utils/Cloning.h"

#include <cctype>
#include <map>
#include <vector>

#define DEBUG_TYPE "lower-varargs"

namespace smack {

using namespace llvm;

namespace {

// The x86-64 `va_list` is { i32 gp_offset; i32 fp_offset; i8*
// overflow_arg_area; i8* reg_save_area; }. Setting both offsets past the end of
// their save areas is what makes clang's lowering take the overflow path for
// every argument, whatever its type, so only the overflow layout has to be
// reproduced here.
const unsigned GP_OFFSET = 0;
const unsigned FP_OFFSET = 4;
const unsigned OVERFLOW_ARG_AREA = 8;
const unsigned REG_SAVE_AREA = 16;
const unsigned GP_EXHAUSTED = 48;
const unsigned FP_EXHAUSTED = 304;

// An argument occupies an eight-byte slot in the overflow area, or two when it
// needs sixteen-byte alignment. Anything else -- a struct or array passed by
// value, whose ABI classification this pass does not reproduce -- is refused,
// and its call site is left exactly as it was.
bool slotSize(Type *T, const DataLayout &DL, uint64_t &Size, Align &Alignment) {
  if (!T->isIntegerTy() && !T->isPointerTy() && !T->isFloatingPointTy())
    return false;
  uint64_t Store = DL.getTypeStoreSize(T);
  if (Store > 16)
    return false;
  Size = Store > 8 ? 16 : 8;
  Alignment = Align(Size);
  return true;
}

bool isVaStart(const Instruction &I) {
  const auto *II = dyn_cast<IntrinsicInst>(&I);
  return II && II->getIntrinsicID() == Intrinsic::vastart;
}

// Whether this call can be specialized: a direct call to a defined variadic
// function, with variadic arguments whose layout we can reproduce.
bool supported(CallInst *CI, Function *F, const DataLayout &DL) {
  if (!F || F->isDeclaration() || !F->isVarArg())
    return false;
  if (CI->getCalledFunction() != F)
    return false;
  if (CI->isMustTailCall())
    return false;
  bool AnyFloat = false, AnyOther = false;
  for (unsigned i = F->arg_size(); i < CI->arg_size(); i++) {
    Type *T = CI->getArgOperand(i)->getType();
    uint64_t Size;
    Align Alignment;
    if (!slotSize(T, DL, Size, Alignment))
      return false;
    (T->isFloatingPointTy() ? AnyFloat : AnyOther) = true;
  }
  // One buffer holding both a floating-point value and an integer or pointer
  // makes sea-DSA collapse its region, and a float access to a region that is
  // not typed float goes through SMACK's deliberately approximate "unsafe"
  // path, so the value does not come back out. Leave such a call alone rather
  // than answer it wrongly; separating those arguments needs storage the ABI
  // lowering would still have to walk contiguously.
  return !(AnyFloat && AnyOther);
}

// Lay the specialized function's extra parameters out in a buffer and point
// the `va_list` at it. The buffer and the stores go in the entry block, so a
// `va_start` inside a loop costs nothing extra; each `va_start` then only
// writes the four list fields.
void lowerVaStart(Function &NF, unsigned FirstExtra, const DataLayout &DL) {
  auto &C = NF.getContext();
  Type *I8 = Type::getInt8Ty(C);
  Type *I8Ptr = Type::getInt8PtrTy(C);
  Type *I32 = Type::getInt32Ty(C);

  std::vector<Instruction *> Starts;
  for (auto &I : instructions(NF))
    if (isVaStart(I))
      Starts.push_back(&I);
  if (Starts.empty())
    return;

  std::vector<uint64_t> Offsets;
  uint64_t Total = 0;
  for (unsigned i = FirstExtra; i < NF.arg_size(); i++) {
    uint64_t Size;
    Align Alignment;
    slotSize(NF.getArg(i)->getType(), DL, Size, Alignment);
    Total = alignTo(Total, Alignment);
    Offsets.push_back(Total);
    Total += Size;
  }
  // A call that passes no variadic argument still needs somewhere to point:
  // reading from it is undefined in C, and leaving the area unallocated would
  // reintroduce the unconstrained read this pass exists to remove.
  if (Total == 0)
    Total = 8;

  IRBuilder<> Entry(&*NF.getEntryBlock().getFirstInsertionPt());
  auto *Buf = Entry.CreateAlloca(ArrayType::get(I8, Total), nullptr, "va.buf");
  Buf->setAlignment(Align(16));
  Value *Base = Entry.CreateBitCast(Buf, I8Ptr);
  for (unsigned i = FirstExtra; i < NF.arg_size(); i++) {
    Argument *A = NF.getArg(i);
    Value *Slot =
        Entry.CreateGEP(I8, Base, Entry.getInt64(Offsets[i - FirstExtra]));
    Entry.CreateStore(A,
                      Entry.CreateBitCast(Slot, A->getType()->getPointerTo()));
  }

  for (Instruction *S : Starts) {
    IRBuilder<> B(S);
    Value *Ap = B.CreateBitCast(cast<CallInst>(S)->getArgOperand(0), I8Ptr);
    auto field = [&](unsigned Off, Type *T) {
      return B.CreateBitCast(B.CreateGEP(I8, Ap, B.getInt64(Off)),
                             T->getPointerTo());
    };
    B.CreateStore(ConstantInt::get(I32, GP_EXHAUSTED), field(GP_OFFSET, I32));
    B.CreateStore(ConstantInt::get(I32, FP_EXHAUSTED), field(FP_OFFSET, I32));
    B.CreateStore(Base, field(OVERFLOW_ARG_AREA, I8Ptr));
    // Never read, since the offsets above send every argument to the overflow
    // area, but left defined so that copying the list copies nothing unknown.
    B.CreateStore(Base, field(REG_SAVE_AREA, I8Ptr));
    S->eraseFromParent();
  }
}

Function *
specialize(Function *F, ArrayRef<Type *> Extra, const DataLayout &DL,
           std::map<std::pair<Function *, std::string>, Function *> &Cache) {
  // The signature becomes part of a Boogie identifier, so the printed LLVM
  // type has to be reduced to characters Boogie accepts: `i32*` would end the
  // identifier at the star and the program would not parse.
  std::string Key;
  raw_string_ostream Sig(Key);
  for (Type *T : Extra)
    T->print(Sig << ".");
  Sig.flush();
  std::string Mangled;
  for (char C : Key)
    Mangled +=
        C == '*' ? 'P'
        : (isalnum(static_cast<unsigned char>(C)) || C == '.' || C == '_')
            ? C
            : '_';
  Key = Mangled;
  auto Found = Cache.find({F, Key});
  if (Found != Cache.end())
    return Found->second;

  std::vector<Type *> Params(F->getFunctionType()->param_begin(),
                             F->getFunctionType()->param_end());
  unsigned FirstExtra = Params.size();
  Params.insert(Params.end(), Extra.begin(), Extra.end());
  auto *NFT = FunctionType::get(F->getReturnType(), Params, false);
  auto *NF = Function::Create(NFT, GlobalValue::InternalLinkage,
                              F->getName() + ".va" + Key, F->getParent());
  NF->copyAttributesFrom(F);
  NF->setIsMaterializable(false);

  ValueToValueMapTy VMap;
  auto NI = NF->arg_begin();
  for (auto &A : F->args()) {
    NI->setName(A.getName());
    VMap[&A] = &*NI++;
  }
  for (unsigned i = 0; i < Extra.size(); i++, ++NI)
    NI->setName("va.arg." + std::to_string(i));

  SmallVector<ReturnInst *, 4> Returns;
  CloneFunctionInto(NF, F, VMap, CloneFunctionChangeType::LocalChangesOnly,
                    Returns);
  // The clone is no longer variadic, so every va_start in it must go; it is
  // replaced by the layout that makes the arguments readable.
  lowerVaStart(*NF, FirstExtra, DL);

  Cache[{F, Key}] = NF;
  return NF;
}

} // namespace

StringRef LowerVarArgs::getPassName() const {
  return "Lower variadic arguments into explicit parameters";
}

void LowerVarArgs::getAnalysisUsage(AnalysisUsage &AU) const {}

bool LowerVarArgs::runOnModule(Module &M) {
  const DataLayout &DL = M.getDataLayout();
  std::map<std::pair<Function *, std::string>, Function *> Cache;
  std::vector<CallInst *> Work;

  for (auto &F : M)
    for (auto &I : instructions(F))
      if (auto *CI = dyn_cast<CallInst>(&I))
        if (supported(CI, CI->getCalledFunction(), DL))
          Work.push_back(CI);

  for (CallInst *CI : Work) {
    Function *F = CI->getCalledFunction();
    std::vector<Type *> Extra;
    std::vector<Value *> Args;
    for (unsigned i = 0; i < CI->arg_size(); i++) {
      Args.push_back(CI->getArgOperand(i));
      if (i >= F->arg_size())
        Extra.push_back(CI->getArgOperand(i)->getType());
    }
    Function *NF = specialize(F, Extra, DL, Cache);

    auto *New = CallInst::Create(NF, Args, "", CI);
    New->setDebugLoc(CI->getDebugLoc());
    SmallVector<std::pair<unsigned, MDNode *>, 4> MDs;
    CI->getAllMetadata(MDs);
    for (auto &MD : MDs)
      New->setMetadata(MD.first, MD.second);
    if (!CI->getType()->isVoidTy()) {
      New->takeName(CI);
      CI->replaceAllUsesWith(New);
    }
    CI->eraseFromParent();
    SDEBUG(errs() << "lowered a variadic call to " << NF->getName() << "\n");
  }

  return !Work.empty();
}

char LowerVarArgs::ID = 0;
static RegisterPass<LowerVarArgs> X("lower-varargs",
                                    "Lower variadic arguments");
} // namespace smack
