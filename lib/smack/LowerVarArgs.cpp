//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/LowerVarArgs.h"
#include "smack/Debug.h"
#include "llvm/ADT/Triple.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Transforms/Utils/Cloning.h"

#include <cctype>
#include <map>
#include <vector>

#define DEBUG_TYPE "lower-varargs"

namespace smack {

using namespace llvm;

namespace {

// The System V x86-64 `va_list` is { i32 gp_offset; i32 fp_offset; i8*
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
const unsigned SLOT_SIZE = 8;

// Windows and the x32 ABI share the architecture but not this `va_list`, so
// the architecture alone does not settle it.
bool hasSysVVaList(const Module &M) {
  Triple T(M.getTargetTriple());
  return T.getArch() == Triple::x86_64 && !T.isOSWindows() &&
         M.getDataLayout().getPointerSize() == 8;
}

// An argument is modeled when it fills one eight-byte slot of the overflow
// area. That leaves out a struct or array passed by value, whose ABI
// classification this pass does not reproduce, and anything wider than a slot,
// such as `long double`: before reading one, clang rounds the list pointer up
// to sixteen bytes with integer arithmetic that SMACK does not resolve, so the
// value would not come back out. A call with such an argument is left exactly
// as it was.
bool fitsInSlot(Type *T, const DataLayout &DL) {
  if (!T->isIntegerTy() && !T->isPointerTy() && !T->isFloatingPointTy())
    return false;
  return DL.getTypeStoreSize(T).getFixedSize() <= SLOT_SIZE;
}

bool isIntrinsic(const Instruction &I, Intrinsic::ID ID) {
  const auto *II = dyn_cast<IntrinsicInst>(&I);
  return II && II->getIntrinsicID() == ID;
}

// The address of the field at `Offset` in the `va_list` that `Ap` points to.
Value *field(IRBuilder<> &B, Value *Ap, unsigned Offset, Type *T) {
  Value *Base = B.CreateBitCast(Ap, B.getInt8PtrTy());
  Value *At = B.CreateGEP(B.getInt8Ty(), Base, B.getInt64(Offset));
  return B.CreateBitCast(At, T->getPointerTo());
}

void copyField(IRBuilder<> &B, Value *To, Value *From, unsigned Offset,
               Type *T) {
  Value *V = B.CreateLoad(T, field(B, From, Offset, T));
  B.CreateStore(V, field(B, To, Offset, T));
}

// Whether this call can be specialized: a direct call to a defined variadic
// function, with variadic arguments whose layout we can reproduce.
bool supported(CallInst *CI, const DataLayout &DL) {
  Function *F = CI->getCalledFunction();
  if (!F || F->isDeclaration() || !F->isVarArg())
    return false;
  if (CI->isMustTailCall())
    return false;
  // Another calling convention, such as `ms_abi`, means another `va_list`.
  if (F->getCallingConv() != CallingConv::C)
    return false;
  bool AnyFloat = false, AnyOther = false;
  for (unsigned i = F->arg_size(); i < CI->arg_size(); i++) {
    // A `byval` operand is the address of the argument, while the ABI puts
    // the argument itself in the overflow area, where the callee reads it.
    // Clang passes a struct this way when it is larger than sixteen bytes,
    // and a smaller one too once the argument registers are used up.
    if (CI->isPassPointeeByValueArgument(i))
      return false;
    Type *T = CI->getArgOperand(i)->getType();
    if (!fitsInSlot(T, DL))
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

// On this target `va_copy` copies the four fields of the list and `va_end`
// does nothing. Clang leaves both as intrinsics, which SMACK does not model,
// so without this a copy of an initialized list would still be unconstrained.
bool lowerVaCopyAndEnd(Module &M) {
  auto &C = M.getContext();
  Type *I8Ptr = Type::getInt8PtrTy(C);
  Type *I32 = Type::getInt32Ty(C);

  std::vector<CallInst *> Copies, Ends;
  for (auto &F : M)
    for (auto &I : instructions(F)) {
      if (isIntrinsic(I, Intrinsic::vacopy))
        Copies.push_back(cast<CallInst>(&I));
      else if (isIntrinsic(I, Intrinsic::vaend))
        Ends.push_back(cast<CallInst>(&I));
    }

  for (CallInst *Copy : Copies) {
    IRBuilder<> B(Copy);
    Value *To = Copy->getArgOperand(0);
    Value *From = Copy->getArgOperand(1);
    copyField(B, To, From, GP_OFFSET, I32);
    copyField(B, To, From, FP_OFFSET, I32);
    copyField(B, To, From, OVERFLOW_ARG_AREA, I8Ptr);
    copyField(B, To, From, REG_SAVE_AREA, I8Ptr);
    Copy->eraseFromParent();
  }
  for (CallInst *End : Ends)
    End->eraseFromParent();
  return !Copies.empty() || !Ends.empty();
}

// Lay the specialized function's extra parameters out in a buffer and point
// the `va_list` at it. The buffer and the stores go in the entry block, so a
// `va_start` inside a loop costs nothing extra; each `va_start` then only
// writes the four list fields.
void lowerVaStart(Function &NF, unsigned FirstExtra) {
  auto &C = NF.getContext();
  Type *I8 = Type::getInt8Ty(C);
  Type *I8Ptr = Type::getInt8PtrTy(C);
  Type *I32 = Type::getInt32Ty(C);

  std::vector<Instruction *> Starts;
  for (auto &I : instructions(NF))
    if (isIntrinsic(I, Intrinsic::vastart))
      Starts.push_back(&I);
  if (Starts.empty())
    return;

  // A call that passes no variadic argument still needs somewhere to point:
  // reading from it is undefined in C, and leaving the area unallocated would
  // reintroduce the unconstrained read this pass exists to remove.
  uint64_t Slots = NF.arg_size() - FirstExtra;
  uint64_t Total = (Slots ? Slots : 1) * SLOT_SIZE;

  IRBuilder<> Entry(&*NF.getEntryBlock().getFirstInsertionPt());
  auto *Buf = Entry.CreateAlloca(ArrayType::get(I8, Total), nullptr, "va.buf");
  Buf->setAlignment(Align(16));
  Value *Base = Entry.CreateBitCast(Buf, I8Ptr);
  for (unsigned i = FirstExtra; i < NF.arg_size(); i++) {
    Argument *A = NF.getArg(i);
    uint64_t Offset = (i - FirstExtra) * SLOT_SIZE;
    Value *Slot = Entry.CreateGEP(I8, Base, Entry.getInt64(Offset));
    Entry.CreateStore(A,
                      Entry.CreateBitCast(Slot, A->getType()->getPointerTo()));
  }

  for (Instruction *S : Starts) {
    IRBuilder<> B(S);
    Value *Ap = cast<CallInst>(S)->getArgOperand(0);
    B.CreateStore(B.getInt32(GP_EXHAUSTED), field(B, Ap, GP_OFFSET, I32));
    B.CreateStore(B.getInt32(FP_EXHAUSTED), field(B, Ap, FP_OFFSET, I32));
    B.CreateStore(Base, field(B, Ap, OVERFLOW_ARG_AREA, I8Ptr));
    // Never read, since the offsets above send every argument to the overflow
    // area, but left defined so that copying the list copies nothing unknown.
    B.CreateStore(Base, field(B, Ap, REG_SAVE_AREA, I8Ptr));
    S->eraseFromParent();
  }
}

// A callee, and the types of the variadic arguments one of its calls passes.
using Signature = std::pair<Function *, std::vector<Type *>>;

Function *specialize(Function *F, const std::vector<Type *> &Extra,
                     std::map<Signature, Function *> &Cache) {
  auto Found = Cache.find({F, Extra});
  if (Found != Cache.end())
    return Found->second;

  // The signature becomes part of a Boogie identifier, so the printed LLVM
  // type has to be reduced to characters Boogie accepts: `i32*` would end the
  // identifier at the star and the program would not parse. Two signatures can
  // reduce to the same text, which is why the cache above is keyed by the
  // types themselves; the module then gives the second clone a name of its own.
  std::string Printed;
  raw_string_ostream Sig(Printed);
  for (Type *T : Extra)
    T->print(Sig << ".");
  Sig.flush();
  std::string Mangled;
  for (char C : Printed)
    Mangled +=
        C == '*' ? 'P'
        : (isalnum(static_cast<unsigned char>(C)) || C == '.' || C == '_')
            ? C
            : '_';

  std::vector<Type *> Params(F->getFunctionType()->param_begin(),
                             F->getFunctionType()->param_end());
  unsigned FirstExtra = Params.size();
  Params.insert(Params.end(), Extra.begin(), Extra.end());
  auto *NFT = FunctionType::get(F->getReturnType(), Params, false);
  auto *NF = Function::Create(NFT, GlobalValue::InternalLinkage,
                              F->getName() + ".va" + Mangled, F->getParent());
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
  lowerVaStart(*NF, FirstExtra);

  Cache[{F, Extra}] = NF;
  return NF;
}

} // namespace

StringRef LowerVarArgs::getPassName() const {
  return "Lower variadic arguments into explicit parameters";
}

void LowerVarArgs::getAnalysisUsage(AnalysisUsage &AU) const {}

bool LowerVarArgs::runOnModule(Module &M) {
  if (!hasSysVVaList(M)) {
    errs() << "warning: lower-varargs has no effect on target '"
           << M.getTargetTriple() << "'\n";
    return false;
  }

  const DataLayout &DL = M.getDataLayout();
  bool Changed = lowerVaCopyAndEnd(M);
  std::map<Signature, Function *> Cache;

  // A clone carries copies of its original's calls, calls to variadic
  // functions among them, so one sweep over the module is not enough: go on
  // until no call is left to rewrite. This ends because a function is cloned
  // at most once for each signature, and a clone brings no call that its
  // original did not have.
  while (true) {
    std::vector<CallInst *> Work;
    for (auto &F : M)
      for (auto &I : instructions(F))
        if (auto *CI = dyn_cast<CallInst>(&I))
          if (supported(CI, DL))
            Work.push_back(CI);
    if (Work.empty())
      break;

    for (CallInst *CI : Work) {
      Function *F = CI->getCalledFunction();
      std::vector<Type *> Extra;
      std::vector<Value *> Args;
      for (unsigned i = 0; i < CI->arg_size(); i++) {
        Args.push_back(CI->getArgOperand(i));
        if (i >= F->arg_size())
          Extra.push_back(CI->getArgOperand(i)->getType());
      }
      Function *NF = specialize(F, Extra, Cache);

      auto *New = CallInst::Create(NF, Args, "", CI);
      New->setAttributes(CI->getAttributes());
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
      SDEBUG(errs() << "lowered a call to " << NF->getName() << "\n");
    }
    Changed = true;
  }

  return Changed;
}

char LowerVarArgs::ID = 0;
static RegisterPass<LowerVarArgs> X("lower-varargs",
                                    "Lower variadic arguments");
} // namespace smack
