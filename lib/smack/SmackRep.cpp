//
// This file is distributed under the MIT License. See LICENSE for details.
//
#define DEBUG_TYPE "smack-rep"
#include "smack/SmackRep.h"
#include "smack/SmackOptions.h"
#include "smack/CodifyStaticInits.h"

namespace smack {

const unsigned MEMORY_INTRINSIC_THRESHOLD = 10;

Regex PROC_MALLOC_FREE("^(malloc|free_)$");
Regex PROC_IGNORE("^("
  "llvm\\.memcpy\\..*|llvm\\.memset\\..*|llvm\\.dbg\\..*|"
  "__SMACK_code|__SMACK_decl|__SMACK_top_decl"
")$");

const vector<unsigned> INTEGER_SIZES = {1, 8, 16, 24, 32, 64, 96, 128};

string indexedName(string name, initializer_list<string> idxs) {
  stringstream idxd;
  idxd << name;
  for (auto idx : idxs)
    idxd << "." << idx;
  return idxd.str();
}

string indexedName(string name, initializer_list<unsigned> idxs) {
  stringstream idxd;
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
          string name = F && F->hasName() ? F->getName().str() : "";
          if (name.find(Naming::CODE_PROC) != string::npos ||
              name.find(Naming::TOP_DECL_PROC) != string::npos ||
              name.find(Naming::DECL_PROC) != string::npos) {
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
    initFuncs.push_back(Naming::STATIC_INIT_PROC);
}

string SmackRep::getString(const llvm::Value* v) {
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

string SmackRep::pointerType() {
  stringstream s;
  s << (SmackOptions::BitPrecisePointers ? "bv" : "i");
  s << ptrSizeInBits;
  return s.str();
}

string SmackRep::intType(unsigned width) {
  if (width == std::numeric_limits<unsigned>::max())
    return "int";
  else
    return (SmackOptions::BitPrecise ? "bv" : "i") + std::to_string(width);
}

string SmackRep::opName(const string& operation, initializer_list<const llvm::Type*> types) {
  stringstream s;
  s << operation;
  for (auto t : types)
    s << "." << type(t);
  return s.str();
}

string SmackRep::opName(const string& operation, initializer_list<unsigned> types) {
  stringstream s;
  s << operation;
  for (auto t : types)
    s << "." << intType(t);
  return s.str();
}

string SmackRep::procName(const llvm::User& U) {
  if (const llvm::CallInst* CI = llvm::dyn_cast<const llvm::CallInst>(&U))
    return procName(U, CI->getCalledFunction());
  else
    assert(false && "Unexpected user expression.");
}

string SmackRep::procName(const llvm::User& U, llvm::Function* F) {
  stringstream name;
  name << naming.get(*F);
  if (F->isVarArg()) {
    for (unsigned i = 0; i < U.getNumOperands()-1; i++)
      name << "." << type(U.getOperand(i)->getType());
  }
  return name.str();
}

string SmackRep::type(const llvm::Type* t) {

  if (t->isFloatingPointTy())
    return Naming::FLOAT_TYPE;

  else if (t->isIntegerTy())
    return intType(t->getIntegerBitWidth());

  else if (t->isPointerTy())
    return Naming::PTR_TYPE;

  else
    // assert(0 && "unsupported type");
    return Naming::PTR_TYPE;
}

string SmackRep::type(const llvm::Value* v) {
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

string SmackRep::memReg(unsigned idx) {
  return indexedName(Naming::MEMORY,{idx});
}

string SmackRep::memType(unsigned region) {
  stringstream s;
  if (!regions.get(region).isSingleton() ||
      (SmackOptions::BitPrecise && SmackOptions::NoByteAccessInference))
    s << "[" << Naming::PTR_TYPE << "] ";
  s << type(regions.get(region).getType());
  return s.str();
}

string SmackRep::memPath(unsigned region) {
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
      pointerLit((unsigned long) llvm::cast<llvm::ConstantInt>(i.getArraySize())->getZExtValue()));

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

  Decl* P = memcpyProc(type(regions.get(r1).getType()), length);
  program.addDecl(P);

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

  Decl* P = memsetProc(type(regions.get(r).getType()), length);
  program.addDecl(P);

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
  assert(CI.getNumArgOperands() == 1 && "Expected one operand.");
  const Value* V = CI.getArgOperand(0);
  while (isa<const CastInst>(V))
    V = dyn_cast<const CastInst>(V)->getOperand(0);
  return Stmt::call(
    indexedName(Naming::VALUE_PROC, {type(V->getType())}),
    vector<const Expr*>({ expr(V) }),
    vector<string>({ naming.get(CI) }));
}

const Stmt* SmackRep::returnValueAnnotation(const CallInst& CI) {
  assert(CI.getNumArgOperands() == 0 && "Expected no operands.");
  Type* T = CI.getParent()->getParent()->getReturnType();
  program.addDecl(
    Decl::procedure(program,
      indexedName(Naming::VALUE_PROC, {type(T)}),
      vector< pair<string,string> >({{"p", type(T)}}),
      vector< pair<string,string> >({{Naming::RET_VAR, Naming::PTR_TYPE}})));
  return Stmt::call(
    indexedName(Naming::VALUE_PROC, {type(T)}),
    vector<const Expr*>({ Expr::id(Naming::RET_VAR) }),
    vector<string>({ naming.get(CI) }));
}

const Stmt* SmackRep::objectAnnotation(const CallInst& CI) {
  assert(CI.getNumArgOperands() == 2 && "Expected two operands.");
  const Value* P = CI.getArgOperand(0);
  const Value* N = CI.getArgOperand(1);
  while (isa<const CastInst>(P))
    P = dyn_cast<const CastInst>(P)->getOperand(0);
  const PointerType* T = dyn_cast<PointerType>(P->getType());
  assert(T && "Expected pointer argument.");

  if (auto I = dyn_cast<ConstantInt>(N)) {
    const unsigned bound = I->getZExtValue();
    const unsigned bits = T->getElementType()->getIntegerBitWidth();
    const unsigned bytes = bits / 8;
    const unsigned length = bound * bytes;
    const unsigned R = regions.idx(P,length);
    bool bytewise = regions.get(R).bytewiseAccess();
    string L = Naming::LOAD + "." + (bytewise ? "bytes." : "") + intType(bits);
    return Stmt::call(Naming::OBJECT_PROC,
      vector<const Expr*>({
        expr(P),
        Expr::lit(bound)
      }),
      vector<string>({ naming.get(CI) }),
      vector<const Attr*>({
        Attr::attr(L, vector<const Expr*>({
          Expr::id(memPath(R)),
          Expr::lit(bytes),
          Expr::lit(length)
        }))
      }));

  } else {
    llvm_unreachable("Non-constant size expression not yet handled.");
  }

}

const Stmt* SmackRep::returnObjectAnnotation(const CallInst& CI) {
  assert(CI.getNumArgOperands() == 1 && "Expected one operand.");
  const Value* V = nullptr; // FIXME GET A VALUE HERE
  assert(V && "Unknown return value.");
  const Value* N = CI.getArgOperand(0);
  const PointerType* T =
    dyn_cast<PointerType>(CI.getParent()->getParent()->getReturnType());
  assert(T && "Expected pointer return type.");

  if (auto I = dyn_cast<ConstantInt>(N)) {
    const unsigned bound = I->getZExtValue();
    const unsigned bits = T->getElementType()->getIntegerBitWidth();
    const unsigned bytes = bits / 8;
    const unsigned length = bound * bytes;
    const unsigned R = regions.idx(V, length);
    bool bytewise = regions.get(R).bytewiseAccess();
    string L = Naming::LOAD + "." + (bytewise ? "bytes." : "") + intType(bits);
    return Stmt::call(Naming::OBJECT_PROC,
      vector<const Expr*>({
        Expr::id(Naming::RET_VAR),
        Expr::lit(bound)
      }),
      vector<string>({ naming.get(CI) }),
      vector<const Attr*>({
        Attr::attr(L, vector<const Expr*>({
          Expr::id(memPath(R)),
          Expr::lit(bytes),
          Expr::lit(length)
        }))
      }));

  } else {
    llvm_unreachable("Non-constant size expression not yet handled.");
  }

}

const Expr* SmackRep::load(const llvm::Value* P) {
  const PointerType* T = dyn_cast<PointerType>(P->getType());
  assert(T && "Expected pointer type.");
  const unsigned R = regions.idx(P);
  const unsigned size = getElementSize(P);
  bool bytewise = regions.get(R).bytewiseAccess();
  bool singleton = regions.get(R).isSingleton();
  const Expr* M = Expr::id(memPath(R));
  string N = Naming::LOAD + "." + (bytewise ? "bytes." : "") +
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
  unsigned size = targetData->getTypeStoreSizeInBits((Type*) T);
  bool bytewise = regions.get(R).bytewiseAccess();
  bool singleton = regions.get(R).isSingleton();

  string N = Naming::STORE + "." + (bytewise ? "bytes." : "") + type(T);
  const Expr* M = Expr::id(memPath(R));
  return Stmt::assign(M, singleton ? V : Expr::fn(N,M,P,V));
}

const Expr* SmackRep::pa(const Expr* base, unsigned long idx, unsigned long size) {
  return pa(base, idx * size);
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
  stringstream fn;
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
    return Expr::fn("$sub.ref", pointerLit(0UL), pointerLit((unsigned long) abs(v)));
}

const Expr* SmackRep::integerLit(unsigned long v, unsigned width) {
  return SmackOptions::BitPrecise ? Expr::lit(v,width) : Expr::lit(v);
}

const Expr* SmackRep::integerLit(long v, unsigned width) {
  if (v >= 0)
    return integerLit((unsigned long) v, width);
  else {
    stringstream op;
    op << "$sub." << (SmackOptions::BitPrecise ? "bv" : "i") << width;
    return Expr::fn(op.str(), integerLit(0UL, width), integerLit((unsigned long) abs(v), width));
  }
}

const Expr* SmackRep::lit(const llvm::Value* v) {
  using namespace llvm;

  if (const ConstantInt* ci = llvm::dyn_cast<const ConstantInt>(v)) {
    const APInt& API = ci->getValue();
    unsigned width = ci->getBitWidth();
    bool neg = width > 1 && ci->isNegative();
    string str = (neg ? API.abs() : API).toString(10,false);
    const Expr* e = SmackOptions::BitPrecise ? Expr::lit(str,width) : Expr::lit(str);
    stringstream op;
    op << "$sub." << (SmackOptions::BitPrecise ? "bv" : "i") << width;
    return neg ? Expr::fn(op.str(), integerLit(0UL,width), e) : e;

  } else if (const ConstantFP* CFP = dyn_cast<const ConstantFP>(v)) {
    const APFloat APF = CFP->getValueAPF();
    string str;
    raw_string_ostream ss(str);
    ss << *CFP;
    istringstream iss(str);
    string float_type;
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

  } else if (llvm::isa<ConstantPointerNull>(v))
    return Expr::id(Naming::NULL_VAL);

  else
    assert( false && "literal type not supported" );
}

const Expr* SmackRep::ptrArith(const llvm::GetElementPtrInst* I) {
  vector< pair<Value*, Type*> > args;
  gep_type_iterator T = gep_type_begin(I);
  for (unsigned i = 1; i < I->getNumOperands(); i++, ++T)
    args.push_back({I->getOperand(i), *T});
  return ptrArith(I->getPointerOperand(), args);
}

const Expr* SmackRep::ptrArith(const llvm::ConstantExpr* CE) {
  assert (CE->getOpcode() == Instruction::GetElementPtr);
  vector< pair<Value*, Type*> > args;
  gep_type_iterator T = gep_type_begin(CE);
  for (unsigned i = 1; i < CE->getNumOperands(); i++, ++T)
    args.push_back({CE->getOperand(i), *T});
  return ptrArith(CE->getOperand(0), args);
}

const Expr* SmackRep::ptrArith(const llvm::Value* p,
    vector< pair<llvm::Value*, llvm::Type*> > args) {
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
      if (const ConstantInt* ci = dyn_cast<ConstantInt>(a.first))
        e = pa(e, (unsigned long) ci->getZExtValue(), storageSize(et));
      else
        e = pa(e, integerToPointer(expr(a.first), a.first->getType()->getIntegerBitWidth()),
          storageSize(et));
    }
  }

  return e;
}

const Expr* SmackRep::expr(const llvm::Value* v) {
  using namespace llvm;

  if (const GlobalValue* g = dyn_cast<const GlobalValue>(v)) {
    assert(g->hasName());
    return Expr::id(naming.get(*v));

  } else if (isa<UndefValue>(v)) {
    string name = naming.get(*v);
    program.addDecl(Decl::constant(name,type(v)));
    return Expr::id(name);

  } else if (naming.get(*v) != "")
    return Expr::id(naming.get(*v));

  else if (const Constant* constant = dyn_cast<const Constant>(v)) {

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
        DEBUG(errs() << "VALUE : " << *v << "\n");
        assert(false && "constant expression of this type not supported");
      }

    } else if (const ConstantInt* ci = dyn_cast<const ConstantInt>(constant)) {
      return lit(ci);

    } else if (const ConstantFP* cf = dyn_cast<const ConstantFP>(constant)) {
      return lit(cf);

    } else if (constant->isNullValue())
      return Expr::id(Naming::NULL_VAL);

    else {
      DEBUG(errs() << "VALUE : " << *v << "\n");
      assert(false && "this type of constant not supported");
    }

  } else {
    DEBUG(errs() << "VALUE : " << *v << "\n");
    assert(false && "value of this type not supported");
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
  string fn = Naming::INSTRUCTION_TABLE.at(opcode);
  return Expr::fn(opName(fn, {t}), expr(lhs), expr(rhs));
}

const Expr* SmackRep::cmp(const llvm::CmpInst* I) {
  return cmp(I->getPredicate(), I->getOperand(0), I->getOperand(1));
}

const Expr* SmackRep::cmp(const llvm::ConstantExpr* CE) {
  return cmp(CE->getPredicate(), CE->getOperand(0), CE->getOperand(1));
}

const Expr* SmackRep::cmp(unsigned predicate, const llvm::Value* lhs, const llvm::Value* rhs) {
  string fn = Naming::CMPINST_TABLE.at(predicate);
  return Expr::fn(opName(fn, {lhs->getType()}), expr(lhs), expr(rhs));
}

Decl* SmackRep::decl(Function* F, CallInst *C) {
  vector< pair<string,string> > params, rets;

  assert (F && "Unknown function call.");

  if (C)
    for (const Value* V : C->arg_operands())
      params.push_back({naming.freshVarName(*V),type(V->getType())});

  else
    for (Function::arg_iterator A = F->arg_begin(); A != F->arg_end(); ++A)
      params.push_back({naming.get(*A), type(A->getType())});

  if (!F->getReturnType()->isVoidTy())
    rets.push_back({Naming::RET_VAR, type(F->getReturnType())});

  return Decl::procedure(program, procName(*C,F), params, rets);
}

vector<Decl*> SmackRep::decl(llvm::Function* F) {
  vector<Decl*> decls;
  string name = naming.get(*F);
  for (auto U : F->users()) {

    if (name == "malloc") {
      llvm::Type* T = F->getFunctionType()->getParamType(0);
      assert (T->isIntegerTy() && "Expected integer argument.");
      unsigned width = T->getIntegerBitWidth();
      decls.push_back(Decl::procedure(program, name, {{"n", type(T)}}, {{"r", Naming::PTR_TYPE}}, {
        Block::block("", { Stmt::call(Naming::ALLOC, {integerToPointer(Expr::id("n"),width)}, {"r"}) })
      }));

    } else if (name == "free_") {
      decls.push_back(Decl::procedure(program, name, {{"n", Naming::PTR_TYPE}}, {}, {
        Block::block("", { Stmt::call(Naming::FREE, {Expr::id("n")}) })
      }));

    } else if (auto C = dyn_cast<CallInst>(U)) {

      // NOTE: it could be that F is used by a call to another function.
      if (C->getCalledFunction() == F)
        decls.push_back(decl(F,C));
      else
        decls.push_back(decl(F,NULL));

    } else if (auto CE = dyn_cast<ConstantExpr>(U)) {
      assert (CE->isCast() && "Expected bitcast.");
      for (auto C : CE->users()) {
        decls.push_back(decl(F,dyn_cast<CallInst>(C)));

        // NOTE: each use ought to have the same type anyways
        break;
      }

    } else {
      decls.push_back(decl(F,NULL));
    }
  }
  return decls;
}

vector<ProcDecl*> SmackRep::proc(llvm::Function* F) {
  vector<ProcDecl*> procs;
  vector< pair<string,string> > params, rets;

  FunctionType* T = F->getFunctionType();

  for (Function::arg_iterator A = F->arg_begin(); A != F->arg_end(); ++A) {
    params.push_back({naming.get(*A), type(A->getType())});
  }

  if (!F->getReturnType()->isVoidTy())
    rets.push_back({Naming::RET_VAR,type(F->getReturnType())});

  if (!F->isVarArg() || F->use_empty()) {
    procs.push_back(static_cast<ProcDecl*>(Decl::procedure(program, naming.get(*F), params, rets)));

  } else {
    // in case this is a vararg function
    for (auto U : F->users()) {
      CallInst* C = dyn_cast<CallInst>(U);

      if (!C || C->getCalledFunction() != F)
        continue;

      vector< pair<string,string> > varArgParams(params);
      for (unsigned i = T->getNumParams(); i < C->getNumArgOperands(); i++) {
        const llvm::Value* V = U->getOperand(i);
        varArgParams.push_back({indexedName("p",{i}),type(V->getType())});
      }

      procs.push_back(static_cast<ProcDecl*>(Decl::procedure(program, procName(*U,F), varArgParams, rets)));
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

  string name = naming.get(*f);
  vector<const Expr*> args;
  vector<string> rets;

  unsigned num_arg_operands = ci.getNumOperands();
  if (isa<CallInst>(ci))
    num_arg_operands -= 1;
  else if (isa<InvokeInst>(ci))
    num_arg_operands -= 3;

  for (unsigned i = 0; i < num_arg_operands; i++)
    args.push_back(arg(f, i, ci.getOperand(i)));

  if (!ci.getType()->isVoidTy())
    rets.push_back(naming.get(ci));

  return Stmt::call(procName(ci, f), args, rets);
}

string SmackRep::code(llvm::CallInst& ci) {

  llvm::Function* f = ci.getCalledFunction();
  assert(f && "Inline code embedded in unresolved function.");

  string fmt = getString(ci.getOperand(0));
  assert(!fmt.empty() && "inline code: missing format string.");

  string s = fmt;
  for (unsigned i=1; i<ci.getNumOperands()-1; i++) {
    const Expr* a = arg(f, i, ci.getOperand(i));
    string::size_type idx = s.find('@');
    assert(idx != string::npos && "inline code: too many arguments.");

    ostringstream ss;
    a->print(ss);
    s = s.replace(idx,1,ss.str());
  }
  return s;
}

string SmackRep::getPrelude() {
  stringstream s;

  s << "// Basic types" << endl;
  for (unsigned size : INTEGER_SIZES)
    s << Decl::typee("i" + std::to_string(size),"int") << endl;
  s << Decl::typee(Naming::PTR_TYPE, pointerType()) << endl;
  s << endl;

  s << "// Basic constants" << endl;
  s << Decl::constant("$0",intType(32)) << endl;
  s << Decl::axiom(Expr::eq(Expr::id("$0"),integerLit(0UL,32))) << endl;

  for (int i=0; i<15; i++)
    s << "const $" << i << ".ref: ref;" << endl;

  for (unsigned i = 0; i < 15; ++i) {
    stringstream t;
    t << "$" << i << ".ref";
    s << Decl::axiom(Expr::eq(Expr::id(t.str()),pointerLit((unsigned long) i))) << endl;
  }
  s << endl;

  s << "// Memory maps (" << regions.size() << " regions)" << endl;
  for (unsigned i=0; i<regions.size(); ++i)
    s << "var " << memPath(i)
      << ": " << memType(i)
      << ";" << endl;

  s << endl;

  s << "// Memory address bounds" << endl;
  s << Decl::axiom(Expr::eq(Expr::id(Naming::GLOBALS_BOTTOM),pointerLit(globalsBottom))) << endl;
  s << Decl::axiom(Expr::eq(Expr::id(Naming::EXTERNS_BOTTOM),pointerLit(externsBottom))) << endl;
  s << Decl::axiom(Expr::eq(Expr::id(Naming::MALLOC_TOP),pointerLit((unsigned long) INT_MAX - 10485760))) << endl;
  s << endl;

  s << "// Bitvector-integer conversions" << endl;
  string b = to_string(ptrSizeInBits);
  string bt = "bv" + b;
  string it = "i" + b;
  s << Decl::function(indexedName("$bv2int",{ptrSizeInBits}), {{"i",bt}}, it, NULL, {Attr::attr("builtin", "bv2int")}) << endl;
  s << Decl::function(indexedName("$int2bv",{ptrSizeInBits}), {{"i",it}}, bt, NULL, {Attr::attr("builtin", "(_ int2bv " + b + ")")}) << endl;
  s << endl;

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

  s << "// Pointer-number conversions" << endl;
  for (unsigned i = 8; i <= 64; i <<= 1) {
    s << Decl::function(indexedName("$p2i", {Naming::PTR_TYPE,intType(i)}), {{"p",Naming::PTR_TYPE}}, intType(i), pointerToInteger(Expr::id("p"),i), {Attr::attr("inline")}) << endl;
    s << Decl::function(indexedName("$i2p", {intType(i),Naming::PTR_TYPE}), {{"i",intType(i)}}, Naming::PTR_TYPE, integerToPointer(Expr::id("i"),i), {Attr::attr("inline")}) << endl;
  }
  s << endl;

  s << "// Pointer predicates" << endl;
  const vector<string> predicates {
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
      << endl;
    s << Decl::function(indexedName(pred,{Naming::PTR_TYPE,Naming::BOOL_TYPE}),
      {{"p1",Naming::PTR_TYPE}, {"p2",Naming::PTR_TYPE}}, Naming::BOOL_TYPE,
      Expr::fn(indexedName(pred,{pointerType(),Naming::BOOL_TYPE}), {Expr::id("p1"),Expr::id("p2")}),
      {Attr::attr("inline")} )
      << endl;
  }
  s << endl;

  s << "// Pointer operations" << endl;
  const vector<string> operations = {"$add", "$sub", "$mul"};
  for (auto op : operations) {
    s << Decl::function(indexedName(op,{Naming::PTR_TYPE}),
      {{"p1",Naming::PTR_TYPE},{"p2",Naming::PTR_TYPE}}, Naming::PTR_TYPE,
      Expr::fn(indexedName(op,{pointerType()}), {Expr::id("p1"), Expr::id("p2")}),
      {Attr::attr("inline")})
      << endl;
  }
  s << endl;

  return s.str();
}

void SmackRep::addBplGlobal(string name) {
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
  ProcDecl* proc = (ProcDecl*) Decl::procedure(program,
    Naming::INITIALIZE_PROC);
  Block* b = Block::block();
  for (auto name : initFuncs)
    b->addStmt(Stmt::call(name));
  b->addStmt(Stmt::return_());
  proc->addBlock(b);
  return proc;
}

vector<Decl*> SmackRep::globalDecl(const llvm::GlobalValue* v) {
  using namespace llvm;
  vector<Decl*> decls;
  vector<const Attr*> ax;
  string name = naming.get(*v);

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

  decls.push_back(Decl::axiom(Expr::eq(
    Expr::id(name),
    pointerLit(external ? externsBottom -= size : globalsBottom -= size) )));

  return decls;
}

const Expr* SmackRep::declareIsExternal(const Expr* e) {
  return Expr::fn(Naming::EXTERNAL_ADDR,e);
}

Decl* SmackRep::memcpyProc(string type, unsigned length) {
  stringstream s;

  string name = Naming::MEMCPY + "." + type;
  if (length < MEMORY_INTRINSIC_THRESHOLD)
    name = name + "." + std::to_string(length);
  else
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

  if (length < MEMORY_INTRINSIC_THRESHOLD) {
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

Decl* SmackRep::memsetProc(string type, unsigned length) {
  stringstream s;

  string name = Naming::MEMSET + "." + type;
  if (length < MEMORY_INTRINSIC_THRESHOLD)
    name = name + "." + std::to_string(length);
  else
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

  if (length < MEMORY_INTRINSIC_THRESHOLD) {
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
