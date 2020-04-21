//
// This file is distributed under the MIT License. See LICENSE for details.
//
#define DEBUG_TYPE "smack-rep"
#include "smack/SmackRep.h"
#include "smack/CodifyStaticInits.h"
#include "smack/SmackOptions.h"
#include "smack/VectorOperations.h"

#include "smack/BoogieAst.h"
#include "smack/Debug.h"
#include "smack/Naming.h"
#include "smack/Regions.h"
#include "smack/SmackWarnings.h"

#include <list>
#include <queue>
#include <set>

namespace {
using namespace llvm;

std::list<CallInst *> findCallers(Function *F) {
  std::list<CallInst *> callers;

  if (F) {
    std::queue<User *> users;
    std::set<User *> covered;

    users.push(F);
    covered.insert(F);

    while (!users.empty()) {
      auto U = users.front();
      users.pop();

      if (CallInst *CI = dyn_cast<CallInst>(U))
        callers.push_back(CI);

      else
        for (auto V : U->users())
          if (!covered.count(V)) {
            users.push(V);
            covered.insert(V);
          }
    }
  }

  return callers;
}
} // namespace

namespace smack {

const unsigned MEMORY_INTRINSIC_THRESHOLD = 0;

std::string indexedName(std::string name,
                        std::initializer_list<std::string> idxs) {
  std::stringstream idxd;
  idxd << name;
  for (auto idx : idxs)
    idxd << "." << idx;
  return idxd.str();
}

std::string indexedName(std::string name,
                        std::initializer_list<unsigned> idxs) {
  std::stringstream idxd;
  idxd << name;
  for (auto idx : idxs)
    idxd << "." << idx;
  return idxd.str();
}

bool isFloat(const llvm::Type *t) { return t->isFloatingPointTy(); }

bool isFloat(const llvm::Value *v) { return isFloat(v->getType()); }

Regex STRING_CONSTANT("^\\.str[0-9]*$");

bool isCodeString(const llvm::Value *V) {
  for (llvm::Value::const_user_iterator U1 = V->user_begin();
       U1 != V->user_end(); ++U1) {
    if (const Constant *C = dyn_cast<const Constant>(*U1)) {
      for (llvm::Value::const_user_iterator U2 = C->user_begin();
           U2 != C->user_end(); ++U2) {
        if (const CallInst *CI = dyn_cast<const CallInst>(*U2)) {
          llvm::Function *F = CI->getCalledFunction();
          std::string name = F && F->hasName() ? F->getName().str() : "";
          if (name.find(Naming::CODE_PROC) != std::string::npos ||
              name.find(Naming::TOP_DECL_PROC) != std::string::npos ||
              name.find(Naming::DECL_PROC) != std::string::npos) {
            return true;
          }
        }
      }
    }
  }
  return false;
}

SmackRep::SmackRep(const DataLayout *L, Naming *N, Program *P, Regions *R)
    : targetData(L), naming(N), program(P), regions(R), globalsOffset(0),
      externsOffset(-32768), uniqueFpNum(0),
      ptrSizeInBits(targetData->getPointerSizeInBits()) {
  if (SmackOptions::MemorySafety)
    initFuncs.push_back("$global_allocations");
  initFuncs.push_back(Naming::STATIC_INIT_PROC);
}

void SmackRep::addAuxiliaryDeclaration(Decl *D) {
  if (auxDecls.count(D->getName()))
    return;
  auxDecls[D->getName()] = D;
}

std::list<Decl *> SmackRep::auxiliaryDeclarations() {
  std::list<Decl *> ds;
  for (auto D : auxDecls)
    ds.push_back(D.second);
  return ds;
}

std::string SmackRep::getString(const llvm::Value *v) {
  if (const llvm::ConstantExpr *constantExpr =
          llvm::dyn_cast<const llvm::ConstantExpr>(v))
    if (constantExpr->getOpcode() == llvm::Instruction::GetElementPtr)
      if (const llvm::GlobalValue *cc = llvm::dyn_cast<const llvm::GlobalValue>(
              constantExpr->getOperand(0)))
        if (const llvm::ConstantDataSequential *cds =
                llvm::dyn_cast<const llvm::ConstantDataSequential>(
                    cc->getOperand(0)))
          return cds->getAsCString();
  return "";
}

unsigned SmackRep::getElementSize(const llvm::Value *v) {
  return getSize(v->getType()->getPointerElementType());
}

unsigned SmackRep::getIntSize(const llvm::Value *v) {
  return getSize(v->getType());
}

unsigned SmackRep::getIntSize(const llvm::Type *t) {
  return t->getIntegerBitWidth();
}

unsigned SmackRep::getSize(llvm::Type *T) {
  return T->isSingleValueType() ? targetData->getTypeSizeInBits(T)
                                : targetData->getTypeStoreSizeInBits(T);
}

std::string SmackRep::pointerType() {
  std::stringstream s;
  s << (SmackOptions::BitPrecisePointers ? "bv" : "i");
  s << ptrSizeInBits;
  return s.str();
}

std::string SmackRep::intType(unsigned width) {
  if (width == std::numeric_limits<unsigned>::max())
    return "int";
  else
    return (SmackOptions::BitPrecise ? "bv" : "i") + std::to_string(width);
}

std::string SmackRep::vectorType(int n, Type *T) {
  std::stringstream s;
  s << Naming::VECTOR_TYPE << "." << n << "x" << type(T);
  return s.str();
}

std::string SmackRep::opName(const std::string &operation,
                             std::list<const llvm::Type *> types) {
  std::stringstream s;
  s << operation;
  for (auto t : types)
    s << "." << type(t);
  return s.str();
}

std::string SmackRep::opName(const std::string &operation,
                             std::initializer_list<unsigned> types) {
  std::stringstream s;
  s << operation;
  for (auto t : types)
    s << "." << intType(t);
  return s.str();
}

std::string SmackRep::procName(const llvm::User &U) {
  if (const llvm::CallInst *CI = llvm::dyn_cast<const llvm::CallInst>(&U))
    return procName(CI->getCalledFunction(), U);
  else
    llvm_unreachable("Unexpected user expression.");
}

std::string SmackRep::procName(llvm::Function *F, const llvm::User &U) {
  std::list<const llvm::Type *> types;
  for (unsigned i = 0; i < U.getNumOperands() - 1; i++)
    types.push_back(U.getOperand(i)->getType());
  return procName(F, types);
}

std::string SmackRep::procName(llvm::Function *F,
                               std::list<const llvm::Type *> types) {
  std::stringstream name;
  name << naming->get(*F);
  if (F->isVarArg())
    for (auto *T : types)
      name << "." << type(T);
  return name.str();
}

std::string SmackRep::type(const llvm::Type *t) {

  if (t->isFloatingPointTy()) {
    if (!SmackOptions::FloatEnabled)
      return Naming::UNINTERPRETED_FLOAT_TYPE;
    if (t->isHalfTy())
      return Naming::HALF_TYPE;
    else if (t->isFloatTy())
      return Naming::FLOAT_TYPE;
    else if (t->isDoubleTy())
      return Naming::DOUBLE_TYPE;
    else if (t->isX86_FP80Ty())
      return Naming::LONG_DOUBLE_TYPE;
    else
      llvm_unreachable("Unsupported floating-point type.");
  }

  else if (t->isIntegerTy())
    return intType(t->getIntegerBitWidth());

  else if (t->isPointerTy())
    return Naming::PTR_TYPE;

  else if (auto VT = dyn_cast<VectorType>(t))
    return vectorType(VT->getNumElements(), VT->getElementType());

  else
    return Naming::PTR_TYPE;
}

std::string SmackRep::type(const llvm::Value *v) { return type(v->getType()); }

unsigned SmackRep::storageSize(llvm::Type *T) {
  return targetData->getTypeStoreSize(T);
}

unsigned SmackRep::offset(llvm::ArrayType *T, unsigned idx) {
  return storageSize(T->getElementType()) * idx;
}

unsigned SmackRep::offset(llvm::StructType *T, unsigned idx) {
  return targetData->getStructLayout(T)->getElementOffset(idx);
}

std::string SmackRep::memReg(unsigned idx) {
  return indexedName(Naming::MEMORY, {idx});
}

std::string SmackRep::memType(unsigned region) {
  std::stringstream s;
  if (!regions->get(region).isSingleton() ||
      (SmackOptions::BitPrecise && SmackOptions::NoByteAccessInference))
    s << "[" << Naming::PTR_TYPE << "] ";
  const Type *T = regions->get(region).getType();
  s << (T ? type(T) : intType(8));
  return s.str();
}

std::string SmackRep::memPath(unsigned region) { return memReg(region); }

std::string SmackRep::memPath(const llvm::Value *v) {
  return memPath(regions->idx(v));
}

std::list<std::pair<std::string, std::string>> SmackRep::memoryMaps() {
  std::list<std::pair<std::string, std::string>> mms;
  for (unsigned i = 0; i < regions->size(); i++)
    mms.push_back({memReg(i), memType(i)});
  return mms;
}

bool SmackRep::isExternal(const llvm::Value *v) {
  return v->getType()->isPointerTy() &&
         !regions->get(regions->idx(v)).isAllocated();
}

const Stmt *SmackRep::alloca(llvm::AllocaInst &i) {
  const Expr *size = Expr::fn(
      "$mul.ref", pointerLit(storageSize(i.getAllocatedType())),
      integerToPointer(expr(i.getArraySize()), getIntSize(i.getArraySize())));

  // TODO this should not be a pointer type.
  return Stmt::call(Naming::ALLOC, {size}, {naming->get(i)});
}

const Stmt *SmackRep::memcpy(const llvm::MemCpyInst &mci) {
  unsigned length;
  if (auto CI = dyn_cast<ConstantInt>(mci.getLength()))
    length = CI->getZExtValue();
  else
    length = std::numeric_limits<unsigned>::max();

  unsigned r1 = regions->idx(mci.getRawDest(), length);
  unsigned r2 = regions->idx(mci.getRawSource(), length);

  const Type *T = regions->get(r1).getType();
  Decl *P = memcpyProc(T ? type(T) : intType(8), length);
  auxDecls[P->getName()] = P;

  const Value *dst = mci.getRawDest(), *src = mci.getRawSource(),
              *len = mci.getLength();

  return Stmt::call(
      P->getName(),
      {Expr::id(memReg(r1)), Expr::id(memReg(r2)), expr(dst), expr(src),
       integerToPointer(expr(len), len->getType()->getIntegerBitWidth()),
       Expr::lit(mci.isVolatile())},
      {memReg(r1)});
}

const Stmt *SmackRep::memset(const llvm::MemSetInst &msi) {
  unsigned length;
  if (auto CI = dyn_cast<ConstantInt>(msi.getLength()))
    length = CI->getZExtValue();
  else
    length = std::numeric_limits<unsigned>::max();

  unsigned r = regions->idx(msi.getRawDest(), length);

  const Type *T = regions->get(r).getType();
  Decl *P = memsetProc(T ? type(T) : intType(8), length);
  auxDecls[P->getName()] = P;

  const Value *dst = msi.getRawDest(), *val = msi.getValue(),
              *len = msi.getLength();

  return Stmt::call(
      P->getName(),
      {Expr::id(memReg(r)), expr(dst), expr(val),
       integerToPointer(expr(len), len->getType()->getIntegerBitWidth()),
       Expr::lit(msi.isVolatile())},
      {memReg(r)});
}

const Stmt *SmackRep::valueAnnotation(const CallInst &CI) {
  std::string name;
  std::list<const Expr *> args({expr(CI.getArgOperand(0))});
  std::list<std::string> rets({naming->get(CI)});
  std::list<const Attr *> attrs;

  assert(CI.getNumArgOperands() > 0 && "Expected at least one argument.");
  assert(CI.getNumArgOperands() <= 2 && "Expected at most two arguments.");
  const Value *V = CI.getArgOperand(0)->stripPointerCasts();

  if (CI.getNumArgOperands() == 1) {
    name = indexedName(Naming::VALUE_PROC, {type(V->getType())});
    if (dyn_cast<const Argument>(V)) {
      attrs.push_back(Attr::attr("name", {Expr::id(naming->get(*V))}));

    } else if (auto LI = dyn_cast<const LoadInst>(V)) {
      auto GEP = dyn_cast<const GetElementPtrInst>(LI->getPointerOperand());
      assert(GEP && "Expected GEP argument to load instruction.");
      auto A = dyn_cast<const Argument>(GEP->getPointerOperand());
      assert(A && "Expected function argument to GEP instruction.");
      auto T = GEP->getResultElementType();
      const unsigned bits = this->getSize(T);
      const unsigned bytes = bits / 8;
      const unsigned R = regions->idx(GEP);
      bool bytewise = regions->get(R).bytewiseAccess();
      attrs.push_back(Attr::attr("name", {Expr::id(naming->get(*A))}));
      attrs.push_back(Attr::attr(
          "field", {
                       Expr::lit(Naming::LOAD + "." +
                                 (bytewise ? "bytes." : "") + intType(bits)),
                       Expr::id(memPath(R)),
                       ptrArith(GEP),
                       Expr::lit(bytes),
                   }));

    } else {
      llvm_unreachable("Unexpected argument type.");
    }

  } else {
    name = Naming::VALUE_PROC + "s";
    const Argument *A;
    Type *T;
    const Expr *addr;

    if ((A = dyn_cast<const Argument>(V))) {
      auto PT = dyn_cast<const PointerType>(A->getType());
      assert(PT && "Expected pointer argument.");
      T = PT->getElementType();
      addr = expr(A);

    } else if (auto GEP = dyn_cast<const GetElementPtrInst>(V)) {
      A = dyn_cast<const Argument>(GEP->getPointerOperand());
      assert(A && "Expected function argument to GEP instruction.");
      T = GEP->getResultElementType();
      addr = ptrArith(GEP);

    } else if (auto LI = dyn_cast<const LoadInst>(V)) {
      auto GEP = dyn_cast<const GetElementPtrInst>(LI->getPointerOperand());
      assert(GEP && "Expected GEP argument to load instruction.");
      A = dyn_cast<const Argument>(GEP->getPointerOperand());
      assert(A && "Expected function argument to GEP instruction.");
      assert(A->hasName() && "Expected named argument.");
      auto PT = dyn_cast<PointerType>(V->getType());
      assert(PT && "Expected pointer type result of load instruction.");
      T = PT->getElementType();
      addr = ptrArith(GEP);

    } else {
      llvm_unreachable("Unexpected argument type.");
    }

    assert(T && "Unkown access type.");
    auto I = dyn_cast<ConstantInt>(CI.getArgOperand(1));
    assert(I && "expected constant size expression.");
    const unsigned count = I->getZExtValue();
    const unsigned bits = this->getSize(T);
    const unsigned bytes = bits / 8;
    const unsigned length = count * bytes;
    const unsigned R = regions->idx(V, length);
    bool bytewise = regions->get(R).bytewiseAccess();
    args.push_back(expr(CI.getArgOperand(1)));
    attrs.push_back(Attr::attr("name", {Expr::id(naming->get(*A))}));
    attrs.push_back(Attr::attr(
        "array",
        {Expr::lit(Naming::LOAD + "." + (bytewise ? "bytes." : "") +
                   intType(bits)),
         Expr::id(memPath(R)), addr, Expr::lit(bytes), Expr::lit(length)}));
  }

  return Stmt::call(name, args, rets, attrs);
}

const Stmt *SmackRep::returnValueAnnotation(const CallInst &CI) {
  assert(CI.getNumArgOperands() == 0 && "Expected no operands.");
  Type *T = CI.getParent()->getParent()->getReturnType();
  std::string name = indexedName(Naming::VALUE_PROC, {type(T)});
  return Stmt::call(name, std::list<const Expr *>({Expr::id(Naming::RET_VAR)}),
                    std::list<std::string>({naming->get(CI)}),
                    {Attr::attr("name", {Expr::id(Naming::RET_VAR)})});
}

// TODO work the following into SmackRep::returnValueAnnotation
// const Stmt* SmackRep::returnObjectAnnotation(const CallInst& CI) {
//   assert(CI.getNumArgOperands() == 1 && "Expected one operand.");
//   const Value* V = nullptr; // FIXME GET A VALUE HERE
//   assert(V && "Unknown return value.");
//   const Value* N = CI.getArgOperand(0);
//   const PointerType* T =
//     dyn_cast<PointerType>(CI.getParent()->getParent()->getReturnType());
//   assert(T && "Expected pointer return type.");
//
//   if (auto I = dyn_cast<ConstantInt>(N)) {
//     const unsigned bound = I->getZExtValue();
//     const unsigned bits = T->getElementType()->getIntegerBitWidth();
//     const unsigned bytes = bits / 8;
//     const unsigned length = bound * bytes;
//     const unsigned R = regions->idx(V, length);
//     bool bytewise = regions->get(R).bytewiseAccess();
//     std::string L = Naming::LOAD + "." + (bytewise ? "bytes." : "") +
//     intType(bits);
//     return Stmt::call(Naming::OBJECT_PROC,
//       std::vector<const Expr*>({
//         Expr::id(Naming::RET_VAR),
//         Expr::lit(bound)
//       }),
//       std::vector<std::string>({ naming->get(CI) }),
//       std::vector<const Attr*>({
//         Attr::attr(L, {
//           Expr::id(memPath(R)),
//           Expr::lit(bytes),
//           Expr::lit(length)
//         })
//       }));
//
//   } else {
//     llvm_unreachable("Non-constant size expression not yet handled.");
//   }
//
// }

bool SmackRep::isUnsafeFloatAccess(const Type *elemTy, const Type *resultTy) {
  if (elemTy->isFloatingPointTy()) {
    bool isByteMap = !resultTy || (resultTy->isIntegerTy() &&
                                   resultTy->getIntegerBitWidth() == 8UL);
    if (isByteMap && !SmackOptions::BitPrecise)
      return true;
    assert(resultTy->isFloatingPointTy() && "Unsupported map result type.");
  }
  return false;
}

const Expr *SmackRep::load(const llvm::Value *P) {
  const PointerType *T = dyn_cast<PointerType>(P->getType());
  assert(T && "Expected pointer type.");
  const unsigned R = regions->idx(P);
  bool bytewise = regions->get(R).bytewiseAccess();
  bool singleton = regions->get(R).isSingleton();
  const Type *resultTy = regions->get(R).getType();
  const Expr *M = Expr::id(memPath(R));
  std::string N =
      Naming::LOAD + "." +
      (bytewise
           ? "bytes."
           : (isUnsafeFloatAccess(T->getElementType(), resultTy) ? "unsafe."
                                                                 : "")) +
      type(T->getElementType());
  return singleton ? M : Expr::fn(N, M, SmackRep::expr(P));
}

const Stmt *SmackRep::store(const Value *P, const Value *V) {
  return store(P, expr(V));
}

const Stmt *SmackRep::store(const Value *P, const Expr *V) {
  const PointerType *T = dyn_cast<PointerType>(P->getType());
  assert(T && "Expected pointer type.");
  return store(regions->idx(P), T->getElementType(), expr(P), V);
}

const Stmt *SmackRep::store(unsigned R, const Type *T, const Expr *P,
                            const Expr *V) {
  bool bytewise = regions->get(R).bytewiseAccess();
  bool singleton = regions->get(R).isSingleton();
  const Type *resultTy = regions->get(R).getType();
  std::string N =
      Naming::STORE + "." +
      (bytewise ? "bytes."
                : (isUnsafeFloatAccess(T, resultTy) ? "unsafe." : "")) +
      type(T);
  const Expr *M = Expr::id(memPath(R));
  return Stmt::assign(M, singleton ? V : Expr::fn(N, M, P, V));
}

const Expr *SmackRep::pa(const Expr *base, long long idx, unsigned size) {
  if (idx >= 0) {
    return pa(base, pointerLit(idx), pointerLit(size));
  } else {
    return pa(base,
              Expr::fn("$sub.ref", pointerLit(0ULL),
                       pointerLit((unsigned long long)std::abs(idx))),
              pointerLit(size));
  }
}

const Expr *SmackRep::pa(const Expr *base, const Expr *idx, unsigned size) {
  return pa(base, idx, pointerLit(size));
}

const Expr *SmackRep::pa(const Expr *base, unsigned long long offset) {
  return offset > 0 ? pa(base, pointerLit(offset)) : base;
}

const Expr *SmackRep::pa(const Expr *base, const Expr *idx, const Expr *size) {
  return pa(base, Expr::fn("$mul.ref", idx, size));
}

const Expr *SmackRep::pa(const Expr *base, const Expr *offset) {
  return Expr::fn("$add.ref", base, offset);
}

const Expr *SmackRep::pointerToInteger(const Expr *e, unsigned width) {
  e = bitConversion(e, SmackOptions::BitPrecisePointers,
                    SmackOptions::BitPrecise);
  if (ptrSizeInBits < width)
    e = Expr::fn(opName("$zext", {ptrSizeInBits, width}), e);
  else if (ptrSizeInBits > width)
    e = Expr::fn(opName("$trunc", {ptrSizeInBits, width}), e);
  return e;
}

const Expr *SmackRep::integerToPointer(const Expr *e, unsigned width) {
  if (width < ptrSizeInBits)
    e = Expr::fn(opName("$zext", {width, ptrSizeInBits}), e);
  else if (width > ptrSizeInBits)
    e = Expr::fn(opName("$trunc", {width, ptrSizeInBits}), e);
  e = bitConversion(e, SmackOptions::BitPrecise,
                    SmackOptions::BitPrecisePointers);
  return e;
}

const Expr *SmackRep::bitConversion(const Expr *e, bool src, bool dst) {
  if (src == dst)
    return e;
  std::stringstream fn;
  fn << (src ? "$bv2int" : "$int2bv") << "." << ptrSizeInBits;
  return Expr::fn(fn.str(), e);
}

const Expr *SmackRep::pointerLit(unsigned long long v) {
  return SmackOptions::BitPrecisePointers ? Expr::lit(v, ptrSizeInBits)
                                          : Expr::lit(v);
}

const Expr *SmackRep::pointerLit(long long v) {
  if (v >= 0)
    return pointerLit((unsigned long long)v);
  else
    return Expr::fn("$sub.ref", pointerLit(0ULL),
                    pointerLit((unsigned long long)std::abs(v)));
}

const Expr *SmackRep::integerLit(unsigned long long v, unsigned width) {
  return SmackOptions::BitPrecise ? Expr::lit(v, width) : Expr::lit(v);
}

const Expr *SmackRep::integerLit(long long v, unsigned width) {
  if (v >= 0)
    return integerLit((unsigned long long)v, width);
  else {
    std::stringstream op;
    op << "$sub." << (SmackOptions::BitPrecise ? "bv" : "i") << width;
    return Expr::fn(op.str(), integerLit(0ULL, width),
                    integerLit((unsigned long long)std::abs(v), width));
  }
}

const Expr *SmackRep::lit(const llvm::Value *v, bool isUnsigned) {
  using namespace llvm;

  if (const ConstantInt *ci = llvm::dyn_cast<const ConstantInt>(v)) {
    const APInt &API = ci->getValue();
    unsigned width = ci->getBitWidth();
    bool neg = isUnsigned ? false : width > 1 && ci->isNegative();
    std::string str = (neg ? API.abs() : API).toString(10, false);
    const Expr *e =
        SmackOptions::BitPrecise ? Expr::lit(str, width) : Expr::lit(str, 0);
    std::stringstream op;
    op << "$sub." << (SmackOptions::BitPrecise ? "bv" : "i") << width;
    return neg ? Expr::fn(op.str(), integerLit(0ULL, width), e) : e;

  } else if (const ConstantFP *CFP = dyn_cast<const ConstantFP>(v)) {
    if (SmackOptions::FloatEnabled) {
      const APFloat APF = CFP->getValueAPF();
      const Type *type = CFP->getType();
      unsigned expSize, sigSize;
      if (type->isHalfTy()) {
        expSize = 5;
        sigSize = 11;
      } else if (type->isFloatTy()) {
        expSize = 8;
        sigSize = 24;
      } else if (type->isDoubleTy()) {
        expSize = 11;
        sigSize = 53;
      } else if (type->isX86_FP80Ty()) {
        expSize = 15;
        sigSize = 65;
      } else {
        llvm_unreachable("Unsupported floating-point type.");
      }
      const APInt API = APF.bitcastToAPInt();
      const APInt exp = API.lshr(sigSize - 1).trunc(expSize);
      APInt sig = API.trunc(sigSize - 1).zext(sigSize);

      if (exp.isAllOnesValue()) {
        if (sig != 0) {
          return Expr::lit("NaN", sigSize, expSize);
        }
        if (API.isNegative()) {
          return Expr::lit("-oo", sigSize, expSize);
        }
        return Expr::lit("+oo", sigSize, expSize);
      }

      if (exp != 0) {
        sig.setBit(sigSize - 1); // hidden bit
      }

      APInt bias = APInt::getSignedMaxValue(expSize);
      if (exp == 0) {
        --bias;
      }

      bool overflow;
      APInt moveDec = exp.usub_ov(bias, overflow);
      moveDec &= APInt(expSize, 3);
      int moveDecAsInt = *moveDec.getRawData();

      APInt finalExp =
          exp.usub_ov(bias, overflow).usub_ov(moveDec, overflow).ashr(2);

      int leftSize = 4 * (moveDecAsInt / 4 + 1);
      int rightSize = 4 * ((sigSize - moveDecAsInt - 2) / 4 + 1);

      sig = sig.zext(leftSize + rightSize + 4)
            << (rightSize - sigSize + moveDecAsInt + 1);

      sig.setBit(sig.getBitWidth() - 1);

      std::string hexSig = sig.toString(16, false).substr(1);
      hexSig.insert(leftSize / 4, ".");

      return Expr::lit(API.isNegative(), hexSig, finalExp.toString(10, true),
                       sigSize, expSize);
    } else {
      const APFloat APF = CFP->getValueAPF();
      std::string str;
      raw_string_ostream ss(str);
      ss << *CFP;
      std::istringstream iss(str);
      std::string float_type;
      long long integerPart, fractionalPart, exponentPart;
      char point, sign, exponent;
      iss >> float_type;
      iss >> integerPart;
      iss >> point;
      iss >> fractionalPart;
      iss >> sign;
      iss >> exponent;
      iss >> exponentPart;

      return Expr::fn("$fp", Expr::lit(integerPart), Expr::lit(fractionalPart),
                      Expr::lit(exponentPart));
    }

  } else if (llvm::isa<ConstantPointerNull>(v))
    return Expr::id(Naming::NULL_VAL);

  else
    llvm_unreachable("Literal type not supported.");
}

const Expr *SmackRep::ptrArith(const llvm::GetElementPtrInst *I) {
  std::vector<std::pair<Value *, gep_type_iterator>> args;
  gep_type_iterator T = gep_type_begin(I);
  for (unsigned i = 1; i < I->getNumOperands(); i++, ++T)
    args.push_back({I->getOperand(i), T});
  return ptrArith(I->getPointerOperand(), args);
}

const Expr *SmackRep::ptrArith(const llvm::ConstantExpr *CE) {
  assert(CE->getOpcode() == Instruction::GetElementPtr);
  std::vector<std::pair<Value *, gep_type_iterator>> args;
  gep_type_iterator T = gep_type_begin(CE);
  for (unsigned i = 1; i < CE->getNumOperands(); i++, ++T)
    args.push_back({CE->getOperand(i), T});
  return ptrArith(CE->getOperand(0), args);
}

const Expr *SmackRep::ptrArith(
    const llvm::Value *p,
    std::vector<std::pair<llvm::Value *, llvm::gep_type_iterator>> args) {
  using namespace llvm;

  const Expr *e = expr(p);

  for (auto a : args) {

    if (StructType *st = a.second.getStructTypeOrNull()) {
      assert(a.first->getType()->isIntegerTy() &&
             a.first->getType()->getPrimitiveSizeInBits() == 32 &&
             "Illegal struct index");
      unsigned fieldNo = dyn_cast<ConstantInt>(a.first)->getZExtValue();
      e = pa(e, offset(st, fieldNo), 1);
    } else {
      Type *et = a.second.getIndexedType();
      assert(a.first->getType()->isIntegerTy() && "Illegal index");
      if (const ConstantInt *ci = dyn_cast<ConstantInt>(a.first)) {
        // First check if the result of multiplication fits in 64 bits
        const APInt &idx = ci->getValue();
        APInt size(idx.getBitWidth(), storageSize(et));
        APInt result = idx * size;
        assert(result.getMinSignedBits() <= 64 &&
               "Index value too large (or too small if negative)");
        e = pa(e, (long long)ci->getSExtValue(), storageSize(et));
      } else
        e = pa(e,
               integerToPointer(expr(a.first),
                                a.first->getType()->getIntegerBitWidth()),
               storageSize(et));
    }
  }

  return e;
}

const Expr *SmackRep::expr(const llvm::Value *v, bool isConstIntUnsigned) {
  using namespace llvm;

  if (isa<const Constant>(v)) {
    v = v->stripPointerCasts();
  }

  if (isa<GlobalValue>(v)) {
    return Expr::id(naming->get(*v));

  } else if (isa<UndefValue>(v)) {
    std::string name = naming->get(*v);
    auxDecls[name] = Decl::constant(name, type(v));
    return Expr::id(name);

  } else if (naming->get(*v) != "") {
    return Expr::id(naming->get(*v));

  } else if (const Constant *constant = dyn_cast<const Constant>(v)) {

    if (const ConstantExpr *CE = dyn_cast<const ConstantExpr>(constant)) {

      if (CE->getOpcode() == Instruction::GetElementPtr)
        return ptrArith(CE);

      else if (CE->isCast())
        return cast(CE);

      else if (Instruction::isBinaryOp(CE->getOpcode()))
        return bop(CE);

      else if (CE->isCompare())
        return cmp(CE);

      else if (CE->getOpcode() == Instruction::Select)
        return select(CE);

      else {
        SDEBUG(errs() << "VALUE : " << *constant << "\n");
        llvm_unreachable("Constant expression of this type not supported.");
      }

    } else if (const ConstantInt *ci = dyn_cast<const ConstantInt>(constant)) {
      return lit(ci, isConstIntUnsigned);

    } else if (const ConstantFP *cf = dyn_cast<const ConstantFP>(constant)) {
      return lit(cf);

    } else if (auto cv = dyn_cast<const ConstantDataVector>(constant)) {
      return VectorOperations(this).constant(cv);

    } else if (auto cd = dyn_cast<const ConstantAggregateZero>(constant)) {
      return VectorOperations(this).constant(cd);

    } else if (constant->isNullValue())
      return Expr::id(Naming::NULL_VAL);

    else {
      SDEBUG(errs() << "VALUE : " << *constant << "\n");
      llvm_unreachable("This type of constant not supported.");
    }

  } else if (isa<InlineAsm>(v)) {
    SmackWarnings::warnUnsound("inline asm passed as argument", nullptr,
                               nullptr);
    return pointerLit(0ULL);

  } else {
    SDEBUG(errs() << "VALUE : " << *v << "\n");
    llvm_unreachable("Value of this type not supported.");
  }
}

const Expr *SmackRep::cast(const llvm::Instruction *I) {
  return cast(I->getOpcode(), I->getOperand(0), I->getType());
}

const Expr *SmackRep::cast(const llvm::ConstantExpr *CE) {
  return cast(CE->getOpcode(), CE->getOperand(0), CE->getType());
}

const Expr *SmackRep::cast(unsigned opcode, const llvm::Value *v,
                           const llvm::Type *t) {
  std::string fn = Naming::INSTRUCTION_TABLE.at(opcode);
  if (opcode == Instruction::FPTrunc || opcode == Instruction::FPExt ||
      opcode == Instruction::SIToFP || opcode == Instruction::UIToFP) {
    if (SmackOptions::FloatEnabled) {
      return Expr::fn(opName(fn, {v->getType(), t}),
                      Expr::id(Naming::RMODE_VAR), expr(v));
    } else {
      return Expr::fn(opName(fn, {v->getType(), t}), expr(v));
    }
  } else if (opcode == Instruction::FPToSI || opcode == Instruction::FPToUI) {
    if (SmackOptions::FloatEnabled) {
      return Expr::fn(opName(fn, {v->getType(), t}), Expr::lit(RModeKind::RTZ),
                      expr(v));
    } else {
      return Expr::fn(opName(fn, {v->getType(), t}), expr(v));
    }
  }
  return Expr::fn(opName(fn, {v->getType(), t}), expr(v));
}

bool SmackRep::isBitwiseOp(llvm::Instruction *I) {
  return I->isShift() || I->isBitwiseLogicOp();
}

bool SmackRep::isFpArithOp(llvm::Instruction *I) {
  return isFpArithOp(I->getOpcode());
}

bool SmackRep::isFpArithOp(unsigned opcode) {
  return opcode == Instruction::FAdd || opcode == Instruction::FSub ||
         opcode == Instruction::FMul || opcode == Instruction::FDiv;
}

const Expr *SmackRep::bop(const llvm::ConstantExpr *CE) {
  return bop(CE->getOpcode(), CE->getOperand(0), CE->getOperand(1),
             CE->getType());
}

const Expr *SmackRep::bop(const llvm::BinaryOperator *BO) {
  return bop(BO->getOpcode(), BO->getOperand(0), BO->getOperand(1),
             BO->getType());
}

const Expr *SmackRep::bop(unsigned opcode, const llvm::Value *lhs,
                          const llvm::Value *rhs, const llvm::Type *t) {
  std::string fn = Naming::INSTRUCTION_TABLE.at(opcode);
  if (isFpArithOp(opcode)) {
    if (SmackOptions::FloatEnabled) {
      return Expr::fn(opName(fn, {t}), Expr::id(Naming::RMODE_VAR), expr(lhs),
                      expr(rhs));
    } else {
      return Expr::fn(opName(fn, {t}), expr(lhs), expr(rhs));
    }
  }
  return Expr::fn(opName(fn, {t}), expr(lhs), expr(rhs));
}

const Expr *SmackRep::getWrappedExpr(const llvm::Value *V, bool isUnsigned) {
  auto rawExpr = expr(V, isUnsigned);
  if (SmackOptions::WrappedIntegerEncoding && V->getType()->isIntegerTy())
    return Expr::fn(opName(Naming::getIntWrapFunc(isUnsigned), {V->getType()}),
                    rawExpr);
  else
    return rawExpr;
}

const Expr *SmackRep::cmp(const llvm::CmpInst *I) {
  return cmp(I->getPredicate(), I->getOperand(0), I->getOperand(1),
             I->isUnsigned());
}

const Expr *SmackRep::cmp(const llvm::ConstantExpr *CE) {
  return cmp(CE->getPredicate(), CE->getOperand(0), CE->getOperand(1), false);
  //           llvm::CmpInst::isUnsigned(CE->getPredicate()));
}

const Expr *SmackRep::cmp(unsigned predicate, const llvm::Value *lhs,
                          const llvm::Value *rhs, bool isUnsigned) {
  std::string fn =
      opName(Naming::CMPINST_TABLE.at(predicate), {lhs->getType()});
  const Expr *e1 = getWrappedExpr(lhs, isUnsigned);
  const Expr *e2 = getWrappedExpr(rhs, isUnsigned);
  if (lhs->getType()->isFloatingPointTy())
    return Expr::ifThenElse(Expr::fn(fn + ".bool", e1, e2), integerLit(1ULL, 1),
                            integerLit(0ULL, 1));
  else
    return Expr::fn(fn, e1, e2);
}

const Expr *SmackRep::select(const llvm::SelectInst *I) {
  return select(I->getCondition(), I->getTrueValue(), I->getFalseValue());
}

const Expr *SmackRep::select(const llvm::ConstantExpr *CE) {
  return select(CE->getOperand(0), CE->getOperand(1), CE->getOperand(2));
}

const Expr *SmackRep::select(const llvm::Value *condVal,
                             const llvm::Value *trueVal,
                             const llvm::Value *falseVal) {
  const Expr *c = expr(condVal), *v1 = expr(trueVal), *v2 = expr(falseVal);

  assert(!condVal->getType()->isVectorTy() &&
         "Vector condition is not supported.");
  return Expr::ifThenElse(Expr::eq(c, integerLit(1LL, 1)), v1, v2);
}

bool SmackRep::isContractExpr(const llvm::Value *V) const {
  auto name = naming->get(*V);
  return isContractExpr(name);
}

bool SmackRep::isContractExpr(const std::string S) const {
  return S.find(Naming::CONTRACT_EXPR) == 0;
}

ProcDecl *SmackRep::procedure(Function *F, CallInst *CI) {
  assert(F && "Unknown function call.");
  std::string name = naming->get(*F);
  std::list<std::pair<std::string, std::string>> params, rets;
  std::list<Decl *> decls;
  std::list<Block *> blocks;

  for (auto &A : F->args())
    params.push_back({naming->get(A), type(A.getType())});

  if (!F->getReturnType()->isVoidTy())
    rets.push_back({Naming::RET_VAR, type(F->getReturnType())});

  if (name == "malloc") {
    Type *W = F->getFunctionType()->getParamType(0);
    assert(W->isIntegerTy() && "Expected integer argument.");
    unsigned width = W->getIntegerBitWidth();
    blocks.push_back(Block::block(
        "",
        {Stmt::call(Naming::MALLOC,
                    {integerToPointer(Expr::id(params.front().first), width)},
                    {Naming::RET_VAR})}));

  } else if (name == "free_") {
    blocks.push_back(Block::block(
        "", {Stmt::call(Naming::FREE, {Expr::id(params.front().first)})}));

  } else if (isContractExpr(F)) {
    for (auto m : memoryMaps())
      params.push_back(m);

  } else if (CI) {
    auto CF = CI->getCalledFunction();

    // Add the parameter from `return_value` calls
    if (CF && CF->getName().equals(Naming::RETURN_VALUE_PROC)) {
      auto T = CI->getParent()->getParent()->getReturnType();
      name = procName(F, {T});
      params.push_back({indexedName("p", {0}), type(T)});

    } else {
      FunctionType *T = F->getFunctionType();
      name = procName(F, *CI);
      for (unsigned i = T->getNumParams(); i < CI->getNumArgOperands(); i++) {
        params.push_back(
            {indexedName("p", {i}), type(CI->getOperand(i)->getType())});
      }
    }
  }

  return static_cast<ProcDecl *>(
      Decl::procedure(name, params, rets, decls, blocks));
}

std::list<ProcDecl *> SmackRep::procedure(llvm::Function *F) {
  std::list<ProcDecl *> procs;
  std::set<std::string> names;
  std::list<CallInst *> callers = findCallers(F);

  // Consider `return_value` calls as normal `value` calls
  if (F->hasName() && F->getName().equals(Naming::VALUE_PROC)) {
    auto more =
        findCallers(F->getParent()->getFunction(Naming::RETURN_VALUE_PROC));
    callers.insert(callers.end(), more.begin(), more.end());
  }

  if (callers.empty() || !F->isVarArg())
    procs.push_back(procedure(F, NULL));

  else
    for (auto CI : callers) {
      auto D = procedure(F, CI);
      if (!names.count(D->getName())) {
        names.insert(D->getName());
        procs.push_back(D);
      }
    }

  return procs;
}

const Expr *SmackRep::arg(llvm::Function *f, unsigned pos, llvm::Value *v) {
  return expr(v);
}

const Stmt *SmackRep::call(llvm::Function *f, const llvm::User &ci) {
  using namespace llvm;

  assert(f && "Call encountered unresolved function.");

  std::string name = naming->get(*f);
  std::list<const Expr *> args;
  std::list<std::string> rets;

  unsigned num_arg_operands = ci.getNumOperands();
  if (isa<CallInst>(ci))
    num_arg_operands -= 1;
  else if (isa<InvokeInst>(ci))
    num_arg_operands -= 3;

  for (unsigned i = 0; i < num_arg_operands; i++)
    args.push_back(arg(f, i, ci.getOperand(i)));

  if (!ci.getType()->isVoidTy())
    rets.push_back(naming->get(ci));

  return Stmt::call(procName(f, ci), args, rets);
}

// we use C-style format characters
// (https://docs.python.org/2.7/library/struct.html#format-characters)
// e.g., @f means the variable is a float
// while @h means the variable is a short
// absence of a format character means use the promoted type as is
std::string SmackRep::code(llvm::CallInst &ci) {

  llvm::Function *f = ci.getCalledFunction();
  assert(f && "Inline code embedded in unresolved function.");

  std::string fmt = getString(ci.getOperand(0));
  assert(!fmt.empty() && "inline code: missing format std::string.");

  std::string s = fmt;
  for (unsigned i = 1; i < ci.getNumOperands() - 1; i++) {
    Value *argV = ci.getOperand(i);
    std::string::size_type idx = s.find('@');
    assert(idx != std::string::npos && "inline code: too many arguments.");

    llvm::Type *targetType = argV->getType();
    bool isCast = false;
    if (idx + 1 < s.length()) {
      switch (s[idx + 1]) {
      case 'c':
      case 'b':
      case 'B':
        targetType = Type::getInt8Ty(argV->getContext());
        isCast = true;
        break;
      case 'f':
        targetType = Type::getFloatTy(argV->getContext());
        isCast = true;
        break;
      case 'h':
      case 'H':
        targetType = Type::getInt16Ty(argV->getContext());
        isCast = true;
        break;
      case 'i':
      case 'I':
        targetType = Type::getInt32Ty(argV->getContext());
        isCast = true;
        break;
      default:
        break;
      }
    }
    if (argV->getType() != targetType) {
      assert(isa<CastInst>(argV) && "Expected a cast expression.");
      CastInst *c = llvm::cast<CastInst>(argV);
      argV = c->getOperand(0);
      assert(argV->getType() == targetType &&
             "Argument type does not match specified type.");
    }

    std::ostringstream ss;
    arg(f, i, argV)->print(ss);
    s = s.replace(idx, (isCast ? 2 : 1), ss.str());
  }
  return s;
}

void SmackRep::addBplGlobal(std::string name) { bplGlobals.push_back(name); }

// Dealing with bitcasts between integers and floating-points
// by adding appropriate assume statements constraining cast inverses
const Stmt *SmackRep::inverseFPCastAssume(const Value *src,
                                          const Type *destType) {
  if (!(SmackOptions::BitPrecise && SmackOptions::FloatEnabled)) {
    return nullptr;
  }
  const Type *srcType = src->getType();
  if (!(srcType->isFloatingPointTy() && destType->isIntegerTy())) {
    return nullptr;
  }
  std::string fn = Naming::INSTRUCTION_TABLE.at(Instruction::BitCast);
  const Expr *srcExpr = expr(src);
  const Expr *castFPToInt =
      Expr::fn(opName(fn, {src->getType(), destType}), srcExpr);
  const Expr *castIntToFP =
      Expr::fn(opName(fn, {destType, src->getType()}), castFPToInt);
  return Stmt::assume(Expr::eq(castIntToFP, srcExpr));
}

const Stmt *SmackRep::inverseFPCastAssume(const StoreInst *si) {
  const Value *P = si->getPointerOperand();
  const PointerType *PT = dyn_cast<PointerType>(P->getType());
  assert(PT && "Expected pointer type.");
  const Type *T = PT->getElementType();
  unsigned R = regions->idx(P);
  if (!T->isFloatingPointTy() || !regions->get(R).bytewiseAccess() ||
      regions->get(R).isSingleton()) {
    return nullptr;
  }
  return inverseFPCastAssume(
      si->getValueOperand(),
      Type::getIntNTy(T->getContext(), T->getPrimitiveSizeInBits()));
}

unsigned SmackRep::numElements(const llvm::Constant *v) {
  using namespace llvm;
  if (const ArrayType *at = dyn_cast<const ArrayType>(v->getType()))
    return at->getNumElements();
  else
    return 1;
}

void SmackRep::addInitFunc(const llvm::Function *f) {
  assert(f->getReturnType()->isVoidTy() &&
         "Init functions cannot return a value");
  assert(f->arg_empty() && "Init functions cannot take parameters");
  initFuncs.push_back(naming->get(*f));
}

Decl *SmackRep::getInitFuncs() {
  ProcDecl *proc = (ProcDecl *)Decl::procedure(Naming::INITIALIZE_PROC);
  Block *b = Block::block();
  for (auto name : initFuncs)
    b->addStmt(Stmt::call(name));
  if (SmackOptions::FloatEnabled) {
    b->addStmt(
        Stmt::assign(Expr::id(Naming::RMODE_VAR), Expr::lit(RModeKind::RNE)));
  }
  b->addStmt(Stmt::return_());
  proc->getBlocks().push_back(b);
  return proc;
}

std::list<Decl *> SmackRep::globalDecl(const llvm::GlobalValue *v) {
  using namespace llvm;
  std::list<Decl *> decls;
  std::list<const Attr *> ax;
  std::string name = naming->get(*v);

  if (isCodeString(v))
    return decls;

  unsigned size = 0;
  bool external = false;

  if (const GlobalVariable *g = dyn_cast<const GlobalVariable>(v)) {
    if (g->hasInitializer()) {
      const Constant *init = g->getInitializer();
      unsigned numElems = numElements(init);

      // NOTE: all global variables have pointer type in LLVM
      if (const PointerType *t = dyn_cast<const PointerType>(g->getType())) {

        // in case we can determine the size of the element type ...
        if (t->getElementType()->isSized())
          size = storageSize(t->getElementType());

        // otherwise (e.g. for function declarations), use a default size
        else
          size = 1024;

      } else
        size = storageSize(g->getType());

      if (!g->hasName() || !STRING_CONSTANT.match(g->getName().str())) {
        if (numElems > 1)
          ax.push_back(Attr::attr("count", numElems));
      }

    } else {
      external = true;
    }
  }

  decls.push_back(Decl::constant(name, Naming::PTR_TYPE, ax, false));

  if (!size)
    size = targetData->getPrefTypeAlignment(v->getType());

  // Add padding between globals to be able to check memory overflows/underflows
  const unsigned globalsPadding = 1024;
  if (external) {
    decls.push_back(Decl::axiom(Expr::eq(
        Expr::id(name), Expr::fn("$add.ref", Expr::id(Naming::GLOBALS_BOTTOM),
                                 pointerLit(externsOffset -= size)))));
  } else {
    decls.push_back(Decl::axiom(Expr::eq(
        Expr::id(name), pointerLit(globalsOffset -= (size + globalsPadding)))));
  }
  globalAllocations[v] = size;

  return decls;
}

const Expr *SmackRep::declareIsExternal(const Expr *e) {
  return Expr::fn(Naming::EXTERNAL_ADDR, e);
}

Decl *SmackRep::memcpyProc(std::string type, unsigned length) {
  std::stringstream s;

  std::string name = Naming::MEMCPY + "." + type;
  bool no_quantifiers = length <= MEMORY_INTRINSIC_THRESHOLD;

  if (no_quantifiers)
    name = name + "." + std::to_string(length);
  SmackWarnings::warnInfo(
      "warning: memory intrinsic length exceeds threshold (" +
      std::to_string(MEMORY_INTRINSIC_THRESHOLD) + "adding quantifiers.");

  s << "procedure " << name << "("
    << "M.dst: [ref] " << type << ", "
    << "M.src: [ref] " << type << ", "
    << "dst: ref, "
    << "src: ref, "
    << "len: ref, "
    << "isvolatile: bool"
    << ") returns ("
    << "M.ret: [ref] " << type << ")";

  if (no_quantifiers) {
    s << "\n"
      << "{"
      << "\n";
    s << "  M.ret := M.dst;"
      << "\n";
    for (unsigned offset = 0; offset < length; ++offset)
      s << "  M.ret[$add.ref(dst," << offset << ")] := "
        << "M.src[$add.ref(src," << offset << ")];"
        << "\n";
    s << "}"
      << "\n";

  } else if (SmackOptions::MemoryModelImpls) {
    s << "\n"
      << "{"
      << "\n";
    s << "  assume (forall x: ref :: "
      << "$sle.ref.bool(dst,x) && $slt.ref.bool(x,$add.ref(dst,len)) ==> "
      << "M.ret[x] == M.src[$add.ref($sub.ref(src,dst),x)]"
      << ");"
      << "\n";
    s << "  assume (forall x: ref :: "
      << "$slt.ref.bool(x,dst) ==> M.ret[x] == M.dst[x]"
      << ");"
      << "\n";
    s << "  assume (forall x: ref :: "
      << "$sle.ref.bool($add.ref(dst,len),x) ==> M.ret[x] == M.dst[x]"
      << ");"
      << "\n";
    s << "}"
      << "\n";

  } else {
    s << ";"
      << "\n";
    s << "ensures (forall x: ref :: "
      << "$sle.ref.bool(dst,x) && $slt.ref.bool(x,$add.ref(dst,len)) ==> "
      << "M.ret[x] == M.src[$add.ref($sub.ref(src,dst),x)]"
      << ");"
      << "\n";
    s << "ensures (forall x: ref :: "
      << "$slt.ref.bool(x,dst) ==> M.ret[x] == M.dst[x]"
      << ");"
      << "\n";
    s << "ensures (forall x: ref :: "
      << "$sle.ref.bool($add.ref(dst,len),x) ==> M.ret[x] == M.dst[x]"
      << ");"
      << "\n";
  }
  return Decl::code(name, s.str());
}

Decl *SmackRep::memsetProc(std::string type, unsigned length) {
  std::stringstream s;

  std::string name = Naming::MEMSET + "." + type;
  bool no_quantifiers = length <= MEMORY_INTRINSIC_THRESHOLD;

  if (no_quantifiers)
    name = name + "." + std::to_string(length);
  SmackWarnings::warnInfo(
      "warning: memory intrinsic length exceeds threshold (" +
      std::to_string(MEMORY_INTRINSIC_THRESHOLD) + "adding quantifiers.");

  s << "procedure " << name << "("
    << "M: [ref] " << type << ", "
    << "dst: ref, "
    << "val: " << intType(8) << ", "
    << "len: ref, "
    << "isvolatile: bool"
    << ") returns ("
    << "M.ret: [ref] " << type << ")";

  if (no_quantifiers) {
    s << "\n"
      << "{"
      << "\n";
    s << "M.ret := M;"
      << "\n";
    for (unsigned offset = 0; offset < length; ++offset)
      s << "  M.ret[$add.ref(dst," << offset << ")] := val;"
        << "\n";
    s << "}"
      << "\n";

  } else if (SmackOptions::MemoryModelImpls) {
    s << "\n"
      << "{"
      << "\n";
    s << "  assume (forall x: ref :: "
      << "$sle.ref.bool(dst,x) && $slt.ref.bool(x,$add.ref(dst,len)) ==> "
      << "M.ret[x] == val"
      << ");"
      << "\n";
    s << "  assume (forall x: ref :: "
      << "$slt.ref.bool(x,dst) ==> M.ret[x] == M[x]"
      << ");"
      << "\n";
    s << "  assume (forall x: ref :: "
      << "$sle.ref.bool($add.ref(dst,len),x) ==> M.ret[x] == M[x]"
      << ");"
      << "\n";
    s << "}"
      << "\n";

  } else {
    s << ";"
      << "\n";
    s << "ensures (forall x: ref :: "
      << "$sle.ref.bool(dst,x) && $slt.ref.bool(x,$add.ref(dst,len)) ==> "
      << "M.ret[x] == val"
      << ");"
      << "\n";
    s << "ensures (forall x: ref :: "
      << "$slt.ref.bool(x,dst) ==> M.ret[x] == M[x]"
      << ");"
      << "\n";
    s << "ensures (forall x: ref :: "
      << "$sle.ref.bool($add.ref(dst,len),x) ==> M.ret[x] == M[x]"
      << ");"
      << "\n";
  }
  return Decl::code(name, s.str());
}

} // namespace smack
