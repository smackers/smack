//
// This file is distributed under the MIT License. See LICENSE for details.
//
#define DEBUG_TYPE "smack-rep"
#include "smack/SmackRep.h"
#include "smack/SmackOptions.h"
#include "smack/CodifyStaticInits.h"
#include <queue>

namespace {
  using namespace llvm;
  using namespace std;

  list<CallInst*> findCallers(Function* F) {
    list<CallInst*> callers;

    if (F) {
      queue<User*> users;
      set<User*> covered;

      users.push(F);
      covered.insert(F);

      while (!users.empty()) {
        auto U = users.front();
        users.pop();

        if (CallInst* CI = dyn_cast<CallInst>(U))
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
}

namespace smack {

const unsigned MEMORY_INTRINSIC_THRESHOLD = 0;

Regex PROC_MALLOC_FREE("^(malloc|free_)$");
Regex PROC_IGNORE("^("
  "llvm\\.memcpy\\..*|llvm\\.memset\\..*|llvm\\.dbg\\..*|"
  "__SMACK_code|__SMACK_decl|__SMACK_top_decl"
")$");

const std::vector<unsigned> INTEGER_SIZES = {1, 8, 16, 24, 32, 40, 48, 56, 64, 88, 96, 128};
const std::vector<unsigned> REF_CONSTANTS = {
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14,
  1024
};

std::string indexedName(std::string name, std::initializer_list<std::string> idxs) {
  std::stringstream idxd;
  idxd << name;
  for (auto idx : idxs)
    idxd << "." << idx;
  return idxd.str();
}

std::string indexedName(std::string name, std::initializer_list<unsigned> idxs) {
  std::stringstream idxd;
  idxd << name;
  for (auto idx : idxs)
    idxd << "." << idx;
  return idxd.str();
}

bool isFloat(const llvm::Type* t) {
  return t->isFloatingPointTy();
}

bool isFloat(const llvm::Value* v) {
  return isFloat(v->getType());
}

Regex STRING_CONSTANT("^\\.str[0-9]*$");

bool isCodeString(const llvm::Value* V) {
  for (llvm::Value::const_user_iterator U1 = V->user_begin(); U1 != V->user_end(); ++U1) {
    if (const Constant* C = dyn_cast<const Constant>(*U1)) {
      for (llvm::Value::const_user_iterator U2 = C->user_begin(); U2 != C->user_end(); ++U2) {
        if (const CallInst* CI = dyn_cast<const CallInst>(*U2)) {
          llvm::Function* F = CI->getCalledFunction();
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

SmackRep::SmackRep(const DataLayout* L, Naming& N, Program& P, Regions& R)
    : targetData(L), naming(N), program(P), regions(R),
      globalsBottom(0), externsBottom(-32768), uniqueFpNum(0),
      ptrSizeInBits(targetData->getPointerSizeInBits())
{
    if (SmackOptions::MemorySafety)
      initFuncs.push_back("$global_allocations");
    initFuncs.push_back(Naming::STATIC_INIT_PROC);
}

std::string SmackRep::getString(const llvm::Value* v) {
  if (const llvm::ConstantExpr* constantExpr = llvm::dyn_cast<const llvm::ConstantExpr>(v))
    if (constantExpr->getOpcode() == llvm::Instruction::GetElementPtr)
      if (const llvm::GlobalValue* cc = llvm::dyn_cast<const llvm::GlobalValue>(constantExpr->getOperand(0)))
        if (const llvm::ConstantDataSequential* cds = llvm::dyn_cast<const llvm::ConstantDataSequential>(cc->getOperand(0)))
          return cds ->getAsCString();
  return "";
}

unsigned SmackRep::getElementSize(const llvm::Value* v) {
  return getSize(v->getType()->getPointerElementType());
}

unsigned SmackRep::getIntSize(const llvm::Value* v) {
  return getSize(v->getType());
}

unsigned SmackRep::getIntSize(const llvm::Type* t) {
  return t->getIntegerBitWidth();
}

unsigned SmackRep::getSize(llvm::Type* T) {
  return T->isSingleValueType()
    ? targetData->getTypeSizeInBits(T)
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

std::string SmackRep::opName(const std::string& operation, std::initializer_list<const llvm::Type*> types) {
  std::stringstream s;
  s << operation;
  for (auto t : types)
    s << "." << type(t);
  return s.str();
}

std::string SmackRep::opName(const std::string& operation, std::initializer_list<unsigned> types) {
  std::stringstream s;
  s << operation;
  for (auto t : types)
    s << "." << intType(t);
  return s.str();
}

std::string SmackRep::procName(const llvm::User& U) {
  if (const llvm::CallInst* CI = llvm::dyn_cast<const llvm::CallInst>(&U))
    return procName(CI->getCalledFunction(), U);
  else
    llvm_unreachable("Unexpected user expression.");
}

std::string SmackRep::procName(llvm::Function* F, const llvm::User& U) {
  std::list<const llvm::Type*> types;
  for (unsigned i = 0; i < U.getNumOperands()-1; i++)
    types.push_back(U.getOperand(i)->getType());
  return procName(F, types);
}

std::string SmackRep::procName(llvm::Function* F, std::list<const llvm::Type*> types) {
  std::stringstream name;
  name << naming.get(*F);
  if (F->isVarArg())
    for (auto* T : types)
      name << "." << type(T);
  return name.str();
}

std::string SmackRep::type(const llvm::Type* t) {

  if (t->isFloatingPointTy()) {
    if (!SmackOptions::BitPrecise)
      return Naming::UNINTERPRETED_FLOAT_TYPE;
    if (t->isFloatTy())
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

  else
    return Naming::PTR_TYPE;
}

std::string SmackRep::type(const llvm::Value* v) {
  return type(v->getType());
}

unsigned SmackRep::storageSize(llvm::Type* T) {
  return targetData->getTypeStoreSize(T);
}

unsigned SmackRep::offset(llvm::ArrayType* T, unsigned idx) {
  return storageSize(T->getElementType()) * idx;
}

unsigned SmackRep::offset(llvm::StructType* T, unsigned idx) {
  return targetData->getStructLayout(T)->getElementOffset(idx);
}

std::string SmackRep::memReg(unsigned idx) {
  return indexedName(Naming::MEMORY,{idx});
}

std::string SmackRep::memType(unsigned region) {
  std::stringstream s;
  if (!regions.get(region).isSingleton() ||
      (SmackOptions::BitPrecise && SmackOptions::NoByteAccessInference))
    s << "[" << Naming::PTR_TYPE << "] ";
  const Type* T = regions.get(region).getType();
  s << (T ? type(T) : intType(8));
  return s.str();
}

std::string SmackRep::memPath(unsigned region) {
  return memReg(region);
}

bool SmackRep::isExternal(const llvm::Value* v) {
  return v->getType()->isPointerTy()
      && !regions.get(regions.idx(v)).isAllocated();
}

const Stmt* SmackRep::alloca(llvm::AllocaInst& i) {
  const Expr* size =
    Expr::fn("$mul.ref",
      pointerLit(storageSize(i.getAllocatedType())),
      integerToPointer(expr(i.getArraySize()), getIntSize(i.getArraySize())));

  // TODO this should not be a pointer type.
  return Stmt::call(Naming::ALLOC,{size},{naming.get(i)});
}

const Stmt* SmackRep::memcpy(const llvm::MemCpyInst& mci) {
  unsigned length;
  if (auto CI = dyn_cast<ConstantInt>(mci.getLength()))
    length = CI->getZExtValue();
  else
    length = std::numeric_limits<unsigned>::max();

  unsigned r1 = regions.idx(mci.getOperand(0),length);
  unsigned r2 = regions.idx(mci.getOperand(1),length);

  const Type* T = regions.get(r1).getType();
  Decl* P = memcpyProc(T ? type(T) : intType(8), length);
  auxDecls[P->getName()] = P;

  const Value
    *dst = mci.getArgOperand(0),
    *src = mci.getArgOperand(1),
    *len = mci.getArgOperand(2),
    *aln = mci.getArgOperand(3),
    *vol = mci.getArgOperand(4);

  return Stmt::call(P->getName(), {
    Expr::id(memReg(r1)),
    Expr::id(memReg(r2)),
    expr(dst),
    expr(src),
    integerToPointer(expr(len), len->getType()->getIntegerBitWidth()),
    integerToPointer(expr(aln), aln->getType()->getIntegerBitWidth()),
    Expr::eq(expr(vol), integerLit(1UL,1))
  }, {memReg(r1)});
}

const Stmt* SmackRep::memset(const llvm::MemSetInst& msi) {
  unsigned length;
  if (auto CI = dyn_cast<ConstantInt>(msi.getLength()))
    length = CI->getZExtValue();
  else
    length = std::numeric_limits<unsigned>::max();

  unsigned r = regions.idx(msi.getOperand(0),length);

  const Type* T = regions.get(r).getType();
  Decl* P = memsetProc(T ? type(T) : intType(8), length);
  auxDecls[P->getName()] = P;

  const Value
    *dst = msi.getArgOperand(0),
    *val = msi.getArgOperand(1),
    *len = msi.getArgOperand(2),
    *aln = msi.getArgOperand(3),
    *vol = msi.getArgOperand(4);

  return Stmt::call(P->getName(), {
    Expr::id(memReg(r)),
    expr(dst),
    expr(val),
    integerToPointer(expr(len), len->getType()->getIntegerBitWidth()),
    integerToPointer(expr(aln), aln->getType()->getIntegerBitWidth()),
    Expr::eq(expr(vol), integerLit(1UL,1))
  }, {memReg(r)});
}

const Stmt* SmackRep::valueAnnotation(const CallInst& CI) {
  std::string name;
  std::list<const Expr*> args({ expr(CI.getArgOperand(0)) });
  std::list<std::string> rets({ naming.get(CI) });
  std::list<const Attr*> attrs;

  assert(CI.getNumArgOperands() > 0 && "Expected at least one argument.");
  assert(CI.getNumArgOperands() <= 2 && "Expected at most two arguments.");
  const Value* V = CI.getArgOperand(0);
  while (isa<const CastInst>(V))
    V = dyn_cast<const CastInst>(V)->getOperand(0);

  if (CI.getNumArgOperands() == 1) {
    name = indexedName(Naming::VALUE_PROC, {type(V->getType())});
    if (dyn_cast<const Argument>(V)) {
      assert(V->hasName() && "Expected named argument.");
      attrs.push_back(Attr::attr("name", {Expr::id(naming.get(*V))}));

    } else if (auto LI = dyn_cast<const LoadInst>(V)) {
      auto GEP = dyn_cast<const GetElementPtrInst>(LI->getPointerOperand());
      assert(GEP && "Expected GEP argument to load instruction.");
      auto A = dyn_cast<const Argument>(GEP->getPointerOperand());
      assert(A && "Expected function argument to GEP instruction.");
      assert(A->hasName() && "Expected named argument.");
      auto T = GEP->getType()->getElementType();
      const unsigned bits = T->getIntegerBitWidth();
      const unsigned bytes = bits / 8;
      const unsigned R = regions.idx(GEP);
      bool bytewise = regions.get(R).bytewiseAccess();
      attrs.push_back(Attr::attr("name", {Expr::id(naming.get(*A))}));
      attrs.push_back(Attr::attr("field", {
        Expr::lit(Naming::LOAD + "." + (bytewise ? "bytes." : "") + intType(bits)),
        Expr::id(memPath(R)),
        ptrArith(GEP),
        Expr::lit(bytes),
      }));

    } else {
      llvm_unreachable("Unexpected argument type.");
    }

  } else {
    name = Naming::VALUE_PROC + "s";
    const Argument* A;
    const Type* T;
    const Expr* addr;

    if ((A = dyn_cast<const Argument>(V))) {
      auto PT = dyn_cast<const PointerType>(A->getType());
      assert(PT && "Expected pointer argument.");
      T = PT->getElementType();
      addr = expr(A);

    } else if (auto GEP = dyn_cast<const GetElementPtrInst>(V)) {
      A = dyn_cast<const Argument>(GEP->getPointerOperand());
      assert(A && "Expected function argument to GEP instruction.");
      T = GEP->getType()->getElementType();
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

    assert(A->hasName() && "Expected named argument.");
    assert(T && "Unkown access type.");
    auto I = dyn_cast<ConstantInt>(CI.getArgOperand(1));
    assert(I && "expected constant size expression.");
    const unsigned count = I->getZExtValue();
    const unsigned bits = T->getIntegerBitWidth();
    const unsigned bytes = bits / 8;
    const unsigned length = count * bytes;
    const unsigned R = regions.idx(V, length);
    bool bytewise = regions.get(R).bytewiseAccess();
    args.push_back(expr(CI.getArgOperand(1)));
    attrs.push_back(Attr::attr("name", {Expr::id(naming.get(*A))}));
    attrs.push_back(Attr::attr("array", {
      Expr::lit(Naming::LOAD + "." + (bytewise ? "bytes." : "") + intType(bits)),
      Expr::id(memPath(R)),
      addr,
      Expr::lit(bytes),
      Expr::lit(length)
    }));
  }

  return Stmt::call(
    name,
    args,
    rets,
    attrs
  );
}

const Stmt* SmackRep::returnValueAnnotation(const CallInst& CI) {
  assert(CI.getNumArgOperands() == 0 && "Expected no operands.");
  Type* T = CI.getParent()->getParent()->getReturnType();
  std::string name = indexedName(Naming::VALUE_PROC, {type(T)});
  return Stmt::call(
    name,
    std::list<const Expr*>({ Expr::id(Naming::RET_VAR) }),
    std::list<std::string>({ naming.get(CI) }),
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
//     const unsigned R = regions.idx(V, length);
//     bool bytewise = regions.get(R).bytewiseAccess();
//     std::string L = Naming::LOAD + "." + (bytewise ? "bytes." : "") + intType(bits);
//     return Stmt::call(Naming::OBJECT_PROC,
//       std::vector<const Expr*>({
//         Expr::id(Naming::RET_VAR),
//         Expr::lit(bound)
//       }),
//       std::vector<std::string>({ naming.get(CI) }),
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

const Expr* SmackRep::load(const llvm::Value* P) {
  const PointerType* T = dyn_cast<PointerType>(P->getType());
  assert(T && "Expected pointer type.");
  const unsigned R = regions.idx(P);
  bool bytewise = regions.get(R).bytewiseAccess();
  bool singleton = regions.get(R).isSingleton();
  const Expr* M = Expr::id(memPath(R));
  std::string N = Naming::LOAD + "." + (bytewise ? "bytes." : "") +
    type(T->getElementType());
  return singleton ? M : Expr::fn(N, M, SmackRep::expr(P));
}

const Stmt* SmackRep::store(const Value* P, const Value* V) {
  return store(P, expr(V));
}

const Stmt* SmackRep::store(const Value* P, const Expr* V) {
  const PointerType* T = dyn_cast<PointerType>(P->getType());
  assert(T && "Expected pointer type.");
  return store(regions.idx(P), T->getElementType(), expr(P), V);
}

const Stmt* SmackRep::store(unsigned R, const Type* T,
    const Expr* P, const Expr* V) {
  bool bytewise = regions.get(R).bytewiseAccess();
  bool singleton = regions.get(R).isSingleton();

  std::string N = Naming::STORE + "." + (bytewise ? "bytes." : "") + type(T);
  const Expr* M = Expr::id(memPath(R));
  return Stmt::assign(M, singleton ? V : Expr::fn(N,M,P,V));
}

const Expr* SmackRep::pa(const Expr* base, long long idx, unsigned long size) {
  if (idx >= 0) {
    return pa(base, idx * size);
  } else {
    return pa(base, Expr::fn("$sub.ref", pointerLit(0UL),
      pointerLit((unsigned long) std::abs(idx))), pointerLit(size));
  }
}

const Expr* SmackRep::pa(const Expr* base, const Expr* idx, unsigned long size) {
  return pa(base, idx, pointerLit(size));
}

const Expr* SmackRep::pa(const Expr* base, unsigned long offset) {
  return offset > 0 ? pa(base, pointerLit(offset)) : base;
}

const Expr* SmackRep::pa(const Expr* base, const Expr* idx, const Expr* size) {
  return pa(base, Expr::fn("$mul.ref", idx, size));
}

const Expr* SmackRep::pa(const Expr* base, const Expr* offset) {
  return Expr::fn("$add.ref", base, offset);
}

const Expr* SmackRep::pointerToInteger(const Expr* e, unsigned width) {
  e = bitConversion(e, SmackOptions::BitPrecisePointers, SmackOptions::BitPrecise);
  if (ptrSizeInBits < width)
    e = Expr::fn(opName("$zext", {ptrSizeInBits, width}), e);
  else if (ptrSizeInBits > width)
    e = Expr::fn(opName("$trunc", {ptrSizeInBits, width}), e);
  return e;
}

const Expr* SmackRep::integerToPointer(const Expr* e, unsigned width) {
  if (width < ptrSizeInBits)
    e = Expr::fn(opName("$zext", {width, ptrSizeInBits}), e);
  else if (width > ptrSizeInBits)
    e = Expr::fn(opName("$trunc", {width, ptrSizeInBits}), e);
  e = bitConversion(e, SmackOptions::BitPrecise, SmackOptions::BitPrecisePointers);
  return e;
}

const Expr* SmackRep::bitConversion(const Expr* e, bool src, bool dst) {
  if (src == dst)
    return e;
  std::stringstream fn;
  fn << (src ? "$bv2int" : "$int2bv") << "." << ptrSizeInBits;
  return Expr::fn(fn.str(), e);
}

const Expr* SmackRep::pointerLit(unsigned long v) {
  return SmackOptions::BitPrecisePointers ? Expr::lit(v,ptrSizeInBits) : Expr::lit(v);
}

const Expr* SmackRep::pointerLit(long v) {
  if (v >= 0)
    return pointerLit((unsigned long) v);
  else
    return Expr::fn("$sub.ref", pointerLit(0UL), pointerLit((unsigned long) std::abs(v)));
}

const Expr* SmackRep::integerLit(unsigned long v, unsigned width) {
  return SmackOptions::BitPrecise ? Expr::lit(v,width) : Expr::lit(v);
}

const Expr* SmackRep::integerLit(long v, unsigned width) {
  if (v >= 0)
    return integerLit((unsigned long) v, width);
  else {
    std::stringstream op;
    op << "$sub." << (SmackOptions::BitPrecise ? "bv" : "i") << width;
    return Expr::fn(op.str(), integerLit(0UL, width), integerLit((unsigned long) std::abs(v), width));
  }
}

const Expr* SmackRep::lit(const llvm::Value* v, bool isUnsigned) {
  using namespace llvm;

  if (const ConstantInt* ci = llvm::dyn_cast<const ConstantInt>(v)) {
    const APInt& API = ci->getValue();
    unsigned width = ci->getBitWidth();
    bool neg = isUnsigned? false : width > 1 && ci->isNegative();
    std::string str = (neg ? API.abs() : API).toString(10,false);
    const Expr* e = SmackOptions::BitPrecise ? Expr::lit(str,width) : Expr::lit(str,0);
    std::stringstream op;
    op << "$sub." << (SmackOptions::BitPrecise ? "bv" : "i") << width;
    return neg ? Expr::fn(op.str(), integerLit(0UL,width), e) : e;

  } else if (const ConstantFP* CFP = dyn_cast<const ConstantFP>(v)) {
    if (SmackOptions::BitPrecise) {
      const APFloat APF = CFP->getValueAPF();
      std::string str;
      raw_string_ostream ss(str);
      ss << *CFP;
      std::istringstream iss(str);
      std::string float_type;
      iss >> float_type;
      unsigned expSize, sigSize;
      if (float_type=="float") {
        expSize = 8;
        sigSize = 24;
      } else if (float_type=="double") {
        expSize = 11;
        sigSize = 53;
      } else {
        llvm_unreachable("Unsupported floating-point type.");
      }
      const APInt API = APF.bitcastToAPInt();
      const APInt n_sign = API.trunc(expSize+sigSize-1);
      const APInt sig = n_sign.trunc(sigSize-1);
      const APInt exp = n_sign.lshr(sigSize-1);
      return Expr::lit(APF.isNegative(), sig.toString(10, false), exp.toString(10, false), sigSize, expSize);
    } else {
      const APFloat APF = CFP->getValueAPF();
      std::string str;
      raw_string_ostream ss(str);
      ss << *CFP;
      std::istringstream iss(str);
      std::string float_type;
      long integerPart, fractionalPart, exponentPart;
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

const Expr* SmackRep::ptrArith(const llvm::GetElementPtrInst* I) {
  std::vector< std::pair<Value*, Type*> > args;
  gep_type_iterator T = gep_type_begin(I);
  for (unsigned i = 1; i < I->getNumOperands(); i++, ++T)
    args.push_back({I->getOperand(i), *T});
  return ptrArith(I->getPointerOperand(), args);
}

const Expr* SmackRep::ptrArith(const llvm::ConstantExpr* CE) {
  assert (CE->getOpcode() == Instruction::GetElementPtr);
  std::vector< std::pair<Value*, Type*> > args;
  gep_type_iterator T = gep_type_begin(CE);
  for (unsigned i = 1; i < CE->getNumOperands(); i++, ++T)
    args.push_back({CE->getOperand(i), *T});
  return ptrArith(CE->getOperand(0), args);
}

const Expr* SmackRep::ptrArith(const llvm::Value* p,
    std::vector< std::pair<llvm::Value*, llvm::Type*> > args) {
  using namespace llvm;

  const Expr* e = expr(p);

  for (auto a : args) {
    if (StructType* st = dyn_cast<StructType>(a.second)) {
      assert(a.first->getType()->isIntegerTy()
        && a.first->getType()->getPrimitiveSizeInBits() == 32
        && "Illegal struct index");
      unsigned fieldNo = dyn_cast<ConstantInt>(a.first)->getZExtValue();
      e = pa(e, offset(st, fieldNo), 1);
    } else {
      Type* et = dyn_cast<SequentialType>(a.second)->getElementType();
      assert(a.first->getType()->isIntegerTy() && "Illegal index");
      if (const ConstantInt* ci = dyn_cast<ConstantInt>(a.first)) {
        assert(ci->getBitWidth() <= 64 && "Unsupported index bitwidth");
        e = pa(e, (long long) ci->getSExtValue(), storageSize(et));
      } else
        e = pa(e, integerToPointer(expr(a.first), a.first->getType()->getIntegerBitWidth()),
          storageSize(et));
    }
  }

  return e;
}

const Expr* SmackRep::expr(const llvm::Value* v, bool isConstIntUnsigned) {
  using namespace llvm;

  if (isa<const Constant>(v)) {
    v = v->stripPointerCasts();
  }

  if (isa<GlobalValue>(v)) {
    assert(v->hasName());
    return Expr::id(naming.get(*v));

  } else if (isa<UndefValue>(v)) {
    std::string name = naming.get(*v);
    auxDecls[name] = Decl::constant(name,type(v));
    return Expr::id(name);

  } else if (naming.get(*v) != "") {
    return Expr::id(naming.get(*v));

  } else if (const Constant* constant = dyn_cast<const Constant>(v)) {

    if (const ConstantExpr* CE = dyn_cast<const ConstantExpr>(constant)) {

      if (CE->getOpcode() == Instruction::GetElementPtr)
        return ptrArith(CE);

      else if (CE->isCast())
        return cast(CE);

      else if (Instruction::isBinaryOp(CE->getOpcode()))
        return bop(CE);

      else if (CE->isCompare())
        return cmp(CE);

      else {
        DEBUG(errs() << "VALUE : " << *constant << "\n");
        llvm_unreachable("Constant expression of this type not supported.");
      }

    } else if (const ConstantInt* ci = dyn_cast<const ConstantInt>(constant)) {
      return lit(ci, isConstIntUnsigned);

    } else if (const ConstantFP* cf = dyn_cast<const ConstantFP>(constant)) {
      return lit(cf);

    } else if (constant->isNullValue())
      return Expr::id(Naming::NULL_VAL);

    else {
      DEBUG(errs() << "VALUE : " << *constant << "\n");
      llvm_unreachable("This type of constant not supported.");
    }

  } else if (isa<InlineAsm>(v)) {
    errs() << "warning: ignoring inline asm passed as argument.\n";
    return pointerLit(0UL);

  } else {
    DEBUG(errs() << "VALUE : " << *v << "\n");
    llvm_unreachable("Value of this type not supported.");
  }
}

const Expr* SmackRep::cast(const llvm::Instruction* I) {
  return cast(I->getOpcode(), I->getOperand(0), I->getType());
}

const Expr* SmackRep::cast(const llvm::ConstantExpr* CE) {
  return cast(CE->getOpcode(), CE->getOperand(0), CE->getType());
}

const Expr* SmackRep::cast(unsigned opcode, const llvm::Value* v, const llvm::Type* t) {
  return Expr::fn(opName(Naming::INSTRUCTION_TABLE.at(opcode), {v->getType(), t}), expr(v));
}

const Expr* SmackRep::bop(const llvm::ConstantExpr* CE) {
  return bop(CE->getOpcode(), CE->getOperand(0), CE->getOperand(1), CE->getType());
}

const Expr* SmackRep::bop(const llvm::BinaryOperator* BO) {
  return bop(BO->getOpcode(), BO->getOperand(0), BO->getOperand(1), BO->getType());
}

const Expr* SmackRep::bop(unsigned opcode, const llvm::Value* lhs, const llvm::Value* rhs, const llvm::Type* t) {
  std::string fn = Naming::INSTRUCTION_TABLE.at(opcode);
  return Expr::fn(opName(fn, {t}), expr(lhs), expr(rhs));
}

const Expr* SmackRep::cmp(const llvm::CmpInst* I) {
  bool isUnsigned = I->isUnsigned();
  return cmp(I->getPredicate(), I->getOperand(0), I->getOperand(1), isUnsigned);
}

const Expr* SmackRep::cmp(const llvm::ConstantExpr* CE) {
  return cmp(CE->getPredicate(), CE->getOperand(0), CE->getOperand(1), false);
}

const Expr* SmackRep::cmp(unsigned predicate, const llvm::Value* lhs, const llvm::Value* rhs, bool isUnsigned) {
  std::string fn = Naming::CMPINST_TABLE.at(predicate);
  return Expr::fn(opName(fn, {lhs->getType()}), expr(lhs, isUnsigned), expr(rhs, isUnsigned));
}

ProcDecl* SmackRep::procedure(Function* F, CallInst* CI) {
  assert(F && "Unknown function call.");
  std::string name = naming.get(*F);
  std::list< std::pair<std::string,std::string> > params, rets;
  std::list<Decl*> decls;
  std::list<Block*> blocks;

  for (auto &A : F->getArgumentList())
    params.push_back({naming.get(A), type(A.getType())});

  if (!F->getReturnType()->isVoidTy())
    rets.push_back({Naming::RET_VAR, type(F->getReturnType())});

  if (name == "malloc") {
    Type* W = F->getFunctionType()->getParamType(0);
    assert(W->isIntegerTy() && "Expected integer argument.");
    unsigned width = W->getIntegerBitWidth();
    blocks.push_back(
      Block::block("", {
        Stmt::call(Naming::MALLOC,
          { integerToPointer(Expr::id(params.front().first), width) },
          { Naming::RET_VAR }
        )
      })
    );

  } else if (name == "free_") {
    blocks.push_back(
      Block::block("", {
        Stmt::call(Naming::FREE, {Expr::id(params.front().first)})
      })
    );

  } else if (name.find(Naming::CONTRACT_EXPR) != std::string::npos) {
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
      FunctionType* T = F->getFunctionType();
      name = procName(F, *CI);
      for (unsigned i = T->getNumParams(); i < CI->getNumArgOperands(); i++) {
        params.push_back({
          indexedName("p",{i}),
          type(CI->getOperand(i)->getType())
        });
      }
    }
  }

  return static_cast<ProcDecl*>(
    Decl::procedure(name, params, rets, decls, blocks)
  );
}

std::list<ProcDecl*> SmackRep::procedure(llvm::Function* F) {
  std::list<ProcDecl*> procs;
  std::set<std::string> names;
  std::list<CallInst*> callers = findCallers(F);

  // Consider `return_value` calls as normal `value` calls
  if (F->hasName() && F->getName().equals(Naming::VALUE_PROC)) {
    auto more = findCallers(F->getParent()->getFunction(Naming::RETURN_VALUE_PROC));
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

const Expr* SmackRep::arg(llvm::Function* f, unsigned pos, llvm::Value* v) {
  return expr(v);
  // (f && f->isVarArg() && isFloat(v))
  //   ? Expr::fn(opName("$fp2si", {v->getType(), f->getType()}), expr(v))
  //   : expr(v);
}

const Stmt* SmackRep::call(llvm::Function* f, const llvm::User& ci) {
  using namespace llvm;

  assert(f && "Call encountered unresolved function.");

  std::string name = naming.get(*f);
  std::list<const Expr*> args;
  std::list<std::string> rets;

  unsigned num_arg_operands = ci.getNumOperands();
  if (isa<CallInst>(ci))
    num_arg_operands -= 1;
  else if (isa<InvokeInst>(ci))
    num_arg_operands -= 3;

  for (unsigned i = 0; i < num_arg_operands; i++)
    args.push_back(arg(f, i, ci.getOperand(i)));

  if (!ci.getType()->isVoidTy())
    rets.push_back(naming.get(ci));

  return Stmt::call(procName(f, ci), args, rets);
}

std::string SmackRep::code(llvm::CallInst& ci) {

  llvm::Function* f = ci.getCalledFunction();
  assert(f && "Inline code embedded in unresolved function.");

  std::string fmt = getString(ci.getOperand(0));
  assert(!fmt.empty() && "inline code: missing format std::string.");

  std::string s = fmt;
  for (unsigned i=1; i<ci.getNumOperands()-1; i++) {
    const Expr* a = arg(f, i, ci.getOperand(i));
    std::string::size_type idx = s.find('@');
    assert(idx != std::string::npos && "inline code: too many arguments.");

    std::ostringstream ss;
    a->print(ss);
    s = s.replace(idx,1,ss.str());
  }
  return s;
}

std::string SmackRep::getPrelude() {
  std::stringstream s;

  s << "// Basic types" << "\n";
  for (unsigned size : INTEGER_SIZES)
    s << Decl::typee("i" + std::to_string(size),"int") << "\n";
  s << Decl::typee(Naming::PTR_TYPE, pointerType()) << "\n";
  if (SmackOptions::FloatEnabled) {
    s << Decl::typee(Naming::FLOAT_TYPE, "float24e8") << "\n";
    s << Decl::typee(Naming::DOUBLE_TYPE, "float53e11") << "\n";
    s << Decl::typee(Naming::LONG_DOUBLE_TYPE, "float65e15") << "\n";
  }
  s << Decl::typee(Naming::UNINTERPRETED_FLOAT_TYPE, intType(32)) << "\n";
  s << "\n";

  s << "// Basic constants" << "\n";
  s << Decl::constant("$0",intType(32)) << "\n";
  s << Decl::axiom(Expr::eq(Expr::id("$0"),integerLit(0UL,32))) << "\n";

  for (unsigned i : REF_CONSTANTS) {
    std::stringstream t;
    s << "const $" << i << ".ref: ref;" << "\n";
    t << "$" << i << ".ref";
    s << Decl::axiom(Expr::eq(Expr::id(t.str()),pointerLit((unsigned long) i))) << "\n";
  }
  s << "\n";

  s << "// Memory maps (" << regions.size() << " regions)" << "\n";
  for (auto M : memoryMaps())
    s << "var " << M.first << ": " << M.second << ";" << "\n";

  s << "\n";

  s << "// Memory address bounds" << "\n";
  s << Decl::axiom(Expr::eq(Expr::id(Naming::GLOBALS_BOTTOM),pointerLit(globalsBottom))) << "\n";
  s << Decl::axiom(Expr::eq(Expr::id(Naming::EXTERNS_BOTTOM),pointerLit(externsBottom))) << "\n";
  unsigned long malloc_top;
  if (ptrSizeInBits == 32)
    malloc_top = 2147483647UL;
  else if (ptrSizeInBits == 64)
    malloc_top = 9223372036854775807UL;
  else
    llvm_unreachable("Unexpected point bit width.");
  s << Decl::axiom(Expr::eq(Expr::id(Naming::MALLOC_TOP),pointerLit(malloc_top))) << "\n";
  s << "\n";

  if (SmackOptions::MemorySafety) {
    s << "// Global allocations" << "\n";
    std::list<const Stmt*> stmts;
    for (auto E : globalAllocations)
      stmts.push_back(Stmt::call("$galloc", {expr(E.first), Expr::lit(E.second)}));
    s << Decl::procedure("$global_allocations", {}, {}, {}, {Block::block("",stmts)}) << "\n";
    s << "\n";
  }

  s << "// Bitstd::vector-integer conversions" << "\n";
  std::string b = std::to_string(ptrSizeInBits);
  std::string bt = "bv" + b;
  std::string it = "i" + b;
  s << Decl::function(indexedName("$int2bv",{ptrSizeInBits}), {{"i",it}}, bt, NULL, {Attr::attr("builtin", "(_ int2bv " + b + ")")}) << "\n";
  if (SmackOptions::BitPrecise) {
    s << Decl::function(indexedName("$bv2uint",{ptrSizeInBits}), {{"i",bt}}, it, NULL, {Attr::attr("builtin", "bv2int")}) << "\n";
    const Expr* arg = Expr::id("i");
    const Expr* uint = Expr::fn(indexedName("$bv2uint", {ptrSizeInBits}), arg);
    std::string offset;
    if (ptrSizeInBits == 32)
      offset = "4294967296";
    else if (ptrSizeInBits == 64)
      offset = "18446744073709551616";
    else
      llvm_unreachable("Unexpected point bit width.");
    s << Decl::function(indexedName("$bv2int",{ptrSizeInBits}), {{"i",bt}}, it, Expr::cond(Expr::fn(indexedName("$slt", {bt, "bool"}), {arg, Expr::lit(0UL, ptrSizeInBits)}), Expr::fn(indexedName("$sub", {it}), {uint, Expr::lit(offset, 0U)}), uint), {Attr::attr("inline")});
  } else
    s << Decl::function(indexedName("$bv2int",{ptrSizeInBits}), {{"i",bt}}, it, NULL, {Attr::attr("builtin", "bv2int")}) << "\n";
  s << "\n";

  if (SmackOptions::BitPrecise) {
    // XXX TODO don’t assume 64-bit pointers TODO XXX
    s << "// Bytewise pointer storage" << "\n";
    s << "function {:inline} $load.bytes.ref(M: [ref] bv8, p: ref) "
      << "returns (ref) { $i2p.bv64.ref($load.bytes.bv64(M, p)) }"
      << "\n";
    s << "function {:inline} $store.bytes.ref(M: [ref] bv8, p: ref, v: ref)"
      << "returns ([ref] bv8) { $store.bytes.bv64(M,p,$p2i.ref.bv64(v)) }"
      << "\n";
  }

  s << "// Pointer-number conversions" << "\n";
  for (unsigned i = 8; i <= 64; i <<= 1) {
    s << Decl::function(indexedName("$p2i", {Naming::PTR_TYPE,intType(i)}), {{"p",Naming::PTR_TYPE}}, intType(i), pointerToInteger(Expr::id("p"),i), {Attr::attr("inline")}) << "\n";
    s << Decl::function(indexedName("$i2p", {intType(i),Naming::PTR_TYPE}), {{"i",intType(i)}}, Naming::PTR_TYPE, integerToPointer(Expr::id("i"),i), {Attr::attr("inline")}) << "\n";
  }
  s << "\n";

  s << "// Pointer predicates" << "\n";
  const std::vector<std::string> predicates {
    "$eq", "$ne", "$ugt", "$uge", "$ult", "$ule", "$sgt", "$sge", "$slt", "$sle"
  };
  for (auto pred : predicates) {
    s << Decl::function(indexedName(pred,{Naming::PTR_TYPE}),
      {{"p1",Naming::PTR_TYPE}, {"p2",Naming::PTR_TYPE}}, intType(1),
      Expr::cond(
        Expr::fn(indexedName(pred,{pointerType(),Naming::BOOL_TYPE}), {Expr::id("p1"),Expr::id("p2")}),
        integerLit(1L,1),
        integerLit(0L,1)),
      {Attr::attr("inline")} )
      << "\n";
    s << Decl::function(indexedName(pred,{Naming::PTR_TYPE,Naming::BOOL_TYPE}),
      {{"p1",Naming::PTR_TYPE}, {"p2",Naming::PTR_TYPE}}, Naming::BOOL_TYPE,
      Expr::fn(indexedName(pred,{pointerType(),Naming::BOOL_TYPE}), {Expr::id("p1"),Expr::id("p2")}),
      {Attr::attr("inline")} )
      << "\n";
  }
  s << "\n";

  s << "// Pointer operations" << "\n";
  const std::vector<std::string> operations = {"$add", "$sub", "$mul"};
  for (auto op : operations) {
    s << Decl::function(indexedName(op,{Naming::PTR_TYPE}),
      {{"p1",Naming::PTR_TYPE},{"p2",Naming::PTR_TYPE}}, Naming::PTR_TYPE,
      Expr::fn(indexedName(op,{pointerType()}), {Expr::id("p1"), Expr::id("p2")}),
      {Attr::attr("inline")})
      << "\n";
  }
  s << "\n";

  return s.str();
}

void SmackRep::addBplGlobal(std::string name) {
  bplGlobals.push_back(name);
}

unsigned SmackRep::numElements(const llvm::Constant* v) {
  using namespace llvm;
  if (const ArrayType* at = dyn_cast<const ArrayType>(v->getType()))
    return at->getNumElements();
  else
    return 1;
}

void SmackRep::addInitFunc(const llvm::Function* f) {
  assert(f->getReturnType()->isVoidTy()
    && "Init functions cannot return a value");
  assert(f->getArgumentList().empty()
    && "Init functions cannot take parameters");
  initFuncs.push_back(naming.get(*f));
}

Decl* SmackRep::getInitFuncs() {
  ProcDecl* proc = (ProcDecl*) Decl::procedure(
    Naming::INITIALIZE_PROC);
  Block* b = Block::block();
  for (auto name : initFuncs)
    b->addStmt(Stmt::call(name));
  b->addStmt(Stmt::return_());
  proc->getBlocks().push_back(b);
  return proc;
}

std::list<Decl*> SmackRep::globalDecl(const llvm::GlobalValue* v) {
  using namespace llvm;
  std::list<Decl*> decls;
  std::list<const Attr*> ax;
  std::string name = naming.get(*v);

  if (isCodeString(v))
    return decls;

  unsigned size = 0;
  bool external = false;

  if (const GlobalVariable* g = dyn_cast<const GlobalVariable>(v)) {
    if (g->hasInitializer()) {
      const Constant* init = g->getInitializer();
      unsigned numElems = numElements(init);

      // NOTE: all global variables have pointer type in LLVM
      if (const PointerType* t = dyn_cast<const PointerType>(g->getType())) {

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
          ax.push_back(Attr::attr("count",numElems));
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
  decls.push_back(Decl::axiom(Expr::eq(
    Expr::id(name),
    pointerLit(external ? externsBottom -= size : globalsBottom -= (size + globalsPadding)) )));

  globalAllocations[v] = size;

  return decls;
}

const Expr* SmackRep::declareIsExternal(const Expr* e) {
  return Expr::fn(Naming::EXTERNAL_ADDR,e);
}

Decl* SmackRep::memcpyProc(std::string type, unsigned length) {
  std::stringstream s;

  std::string name = Naming::MEMCPY + "." + type;
  bool no_quantifiers = length <= MEMORY_INTRINSIC_THRESHOLD;

  if (no_quantifiers)
    name = name + "." + std::to_string(length);
  else if (SmackOptions::Warnings)
    errs() << "warning: memory intrinsic length exceeds threshold ("
           << MEMORY_INTRINSIC_THRESHOLD << "); "
           << "adding quantifiers.\n";

  s << "procedure " << name << "("
    << "M.dst: [ref] " << type << ", "
    << "M.src: [ref] " << type << ", "
    << "dst: ref, "
    << "src: ref, "
    << "len: ref, "
    << "align: ref, "
    << "isvolatile: bool"
    << ") returns ("
    << "M.ret: [ref] " << type
    << ")";

  if (no_quantifiers) {
    s << "\n" << "{" << "\n";
    s << "  M.ret := M.dst;" << "\n";
    for (unsigned offset = 0; offset < length; ++offset)
      s << "  M.ret[$add.ref(dst," << offset << ")] := "
        << "M.src[$add.ref(src," << offset << ")];" << "\n";
    s << "}" << "\n";

  } else if (SmackOptions::MemoryModelImpls) {
    s << "\n" << "{" << "\n";
    s << "  assume (forall x: ref :: "
      << "$sle.ref.bool(dst,x) && $slt.ref.bool(x,$add.ref(dst,len)) ==> "
      << "M.ret[x] == M.src[$add.ref($sub.ref(src,dst),x)]"
      << ");" << "\n";
    s << "  assume (forall x: ref :: "
      << "$slt.ref.bool(x,dst) ==> M.ret[x] == M.dst[x]"
      << ");" << "\n";
    s << "  assume (forall x: ref :: "
      << "$sle.ref.bool($add.ref(dst,len),x) ==> M.ret[x] == M.dst[x]"
      << ");" << "\n";
    s << "}" << "\n";

  } else {
    s << ";" << "\n";
    s << "ensures (forall x: ref :: "
      << "$sle.ref.bool(dst,x) && $slt.ref.bool(x,$add.ref(dst,len)) ==> "
      << "M.ret[x] == M.src[$add.ref($sub.ref(src,dst),x)]"
      << ");" << "\n";
    s << "ensures (forall x: ref :: "
      << "$slt.ref.bool(x,dst) ==> M.ret[x] == M.dst[x]"
      << ");" << "\n";
    s << "ensures (forall x: ref :: "
      << "$sle.ref.bool($add.ref(dst,len),x) ==> M.ret[x] == M.dst[x]"
      << ");" << "\n";
  }
  return Decl::code(name, s.str());
}

Decl* SmackRep::memsetProc(std::string type, unsigned length) {
  std::stringstream s;

  std::string name = Naming::MEMSET + "." + type;
  bool no_quantifiers = length <= MEMORY_INTRINSIC_THRESHOLD;

  if (no_quantifiers)
    name = name + "." + std::to_string(length);
  else if (SmackOptions::Warnings)
    errs() << "warning: memory intrinsic length exceeds threshold ("
           << MEMORY_INTRINSIC_THRESHOLD << "); "
           << "adding quantifiers.\n";

  s << "procedure " << name << "("
    << "M: [ref] " << type << ", "
    << "dst: ref, "
    << "val: " << intType(8) << ", "
    << "len: ref, "
    << "align: ref, "
    << "isvolatile: bool"
    << ") returns ("
    << "M.ret: [ref] " << type
    << ")";

  if (no_quantifiers) {
    s << "\n" << "{" << "\n";
    s << "M.ret := M;" << "\n";
    for (unsigned offset = 0; offset < length; ++offset)
      s << "  M.ret[$add.ref(dst," << offset << ")] := val;" << "\n";
    s << "}" << "\n";

  } else if (SmackOptions::MemoryModelImpls) {
    s << "\n" << "{" << "\n";
    s << "  assume (forall x: ref :: "
      << "$sle.ref.bool(dst,x) && $slt.ref.bool(x,$add.ref(dst,len)) ==> "
      << "M.ret[x] == val"
      << ");" << "\n";
    s << "  assume (forall x: ref :: "
      << "$slt.ref.bool(x,dst) ==> M.ret[x] == M[x]"
      << ");" << "\n";
    s << "  assume (forall x: ref :: "
      << "$sle.ref.bool($add.ref(dst,len),x) ==> M.ret[x] == M[x]"
      << ");" << "\n";
    s << "}" << "\n";

  } else {
    s << ";" << "\n";
    s << "ensures (forall x: ref :: "
      << "$sle.ref.bool(dst,x) && $slt.ref.bool(x,$add.ref(dst,len)) ==> "
      << "M.ret[x] == val"
      << ");" << "\n";
    s << "ensures (forall x: ref :: "
      << "$slt.ref.bool(x,dst) ==> M.ret[x] == M[x]"
      << ");" << "\n";
    s << "ensures (forall x: ref :: "
      << "$sle.ref.bool($add.ref(dst,len),x) ==> M.ret[x] == M[x]"
      << ");" << "\n";
  }
  return Decl::code(name, s.str());
}

} // namespace smack
