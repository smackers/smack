//
// This file is distributed under the MIT License. See LICENSE for details.
//
#define DEBUG_TYPE "smack-rep"
#include "smack/SmackRep.h"
#include "smack/SmackOptions.h"

namespace smack {

const string SmackRep::BOOL_TYPE = "bool";
const string SmackRep::FLOAT_TYPE = "float";
const string SmackRep::PTR_TYPE = "ref";

const string SmackRep::NULL_VAL = "$0.ref";
const string SmackRep::GLOBALS_BOTTOM = "$GLOBALS_BOTTOM";
const string SmackRep::EXTERNS_BOTTOM = "$EXTERNS_BOTTOM";
const string SmackRep::MALLOC_TOP = "$MALLOC_TOP";

const string SmackRep::ALLOCA = "$alloca";
const string SmackRep::MALLOC = "$malloc";
const string SmackRep::FREE = "$free";
const string SmackRep::MEMCPY = "$memcpy";

// used for memory model debugging
const string SmackRep::MEM_OP = "$mop";
const string SmackRep::REC_MEM_OP = "boogie_si_record_mop";
const string SmackRep::MEM_OP_VAL = "$MOP";

const string SmackRep::STATIC_INIT = "$static_init";
const string SmackRep::INIT_FUNCS = "$init_funcs";

Regex PROC_MALLOC_FREE("^(malloc|free_)$");
Regex PROC_IGNORE("^("
  "llvm\\.memcpy\\..*|llvm\\.memset\\..*|llvm\\.dbg\\..*|"
  "__SMACK_code|__SMACK_decl|__SMACK_top_decl"
")$");

const map<unsigned,string> SmackRep::INSTRUCTION_TABLE {
  {Instruction::Trunc, "$trunc"},
  {Instruction::ZExt, "$zext"},
  {Instruction::SExt, "$sext"},
  {Instruction::FPTrunc, "$fptrunc"},
  {Instruction::FPExt, "$fpext"},
  {Instruction::BitCast, "$bitcast"},
  {Instruction::FPToUI, "$fp2ui"},
  {Instruction::FPToSI, "$fp2si"},
  {Instruction::UIToFP, "$ui2fp"},
  {Instruction::SIToFP, "$si2fp"},
  {Instruction::PtrToInt, "$p2i"},
  {Instruction::IntToPtr, "$i2p"},
  {Instruction::Add, "$add"},
  {Instruction::Sub, "$sub"},
  {Instruction::Mul, "$mul"},
  {Instruction::SDiv, "$sdiv"},
  {Instruction::UDiv, "$udiv"},
  {Instruction::SRem, "$srem"},
  {Instruction::URem, "$urem"},
  {Instruction::And, "$and"},
  {Instruction::Or, "$or"},
  {Instruction::Xor, "$xor"},
  {Instruction::LShr, "$lshr"},
  {Instruction::AShr, "$ashr"},
  {Instruction::Shl, "$shl"},
  {Instruction::FAdd, "$fadd"},
  {Instruction::FSub, "$fsub"},
  {Instruction::FMul, "$fmul"},
  {Instruction::FDiv, "$fdiv"},
  {Instruction::FRem, "$frem"}
};

const map<unsigned,string> SmackRep::CMPINST_TABLE {
  {CmpInst::ICMP_EQ, "$eq"},
  {CmpInst::ICMP_NE, "$ne"},
  {CmpInst::ICMP_SGE, "$sge"},
  {CmpInst::ICMP_UGE, "$uge"},
  {CmpInst::ICMP_SLE, "$sle"},
  {CmpInst::ICMP_ULE, "$ule"},
  {CmpInst::ICMP_SLT, "$slt"},
  {CmpInst::ICMP_ULT, "$ult"},
  {CmpInst::ICMP_SGT, "$sgt"},
  {CmpInst::ICMP_UGT, "$ugt"},
  {CmpInst::FCMP_FALSE, "$ffalse"},
  {CmpInst::FCMP_OEQ, "$foeq"},
  {CmpInst::FCMP_OGE, "$foge"},
  {CmpInst::FCMP_OGT, "$fogt"},
  {CmpInst::FCMP_OLE, "$fole"},
  {CmpInst::FCMP_OLT, "$folt"},
  {CmpInst::FCMP_ONE, "$fone"},
  {CmpInst::FCMP_ORD, "$ford"},
  {CmpInst::FCMP_TRUE, "$ftrue"},
  {CmpInst::FCMP_UEQ, "$fueq"},
  {CmpInst::FCMP_UGE, "$fuge"},
  {CmpInst::FCMP_UGT, "$fugt"},
  {CmpInst::FCMP_ULE, "$fule"},
  {CmpInst::FCMP_ULT, "$fult"},
  {CmpInst::FCMP_UNE, "$fune"},
  {CmpInst::FCMP_UNO, "$funo"}
};

const map<unsigned,string> SmackRep::ATOMICRMWINST_TABLE {
  {AtomicRMWInst::Add, "$add"},
  {AtomicRMWInst::Sub, "$sub"},
  {AtomicRMWInst::And, "$and"},
  {AtomicRMWInst::Nand, "$nand"},
  {AtomicRMWInst::Or, "$or"},
  {AtomicRMWInst::Xor, "$xor"},
  {AtomicRMWInst::Max, "$smax"},
  {AtomicRMWInst::Min, "$smin"},
  {AtomicRMWInst::UMax, "$umax"},
  {AtomicRMWInst::UMin, "$umin"}
};

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
          if (name.find("__SMACK_code") != string::npos ||
              name.find("__SMACK_top_decl") != string::npos ||
              name.find("__SMACK_decl") != string::npos) {
            return true;
          }
        }
      }
    }
  }
  return false;
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

unsigned SmackRep::getSize(llvm::Type* t) {
  unsigned size = 0;
  if (t->isSingleValueType())
    size = targetData->getTypeSizeInBits(t);
  return size;
}

string SmackRep::pointerType() {
  stringstream s;
  s << (SmackOptions::BitPrecisePointers ? "bv" : "i");
  s << ptrSizeInBits;
  return s.str();
}

string SmackRep::intType(unsigned width) {
  stringstream s;
  s << (SmackOptions::BitPrecise ? "bv" : "i");
  s << width;
  return s.str();
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
    return FLOAT_TYPE;

  else if (t->isIntegerTy())
    return intType(t->getIntegerBitWidth());

  else if (t->isPointerTy())
    return PTR_TYPE;

  else
    // assert(0 && "unsupported type");
    return PTR_TYPE;
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
  return indexedName("$M",{idx});
}

bool SmackRep::uniformMemoryAccesses() {
  return !SmackOptions::BitPrecise || SmackOptions::NoByteAccessInference;
}

bool SmackRep::bytewiseAccess(const GlobalValue* V, unsigned offset) {
  return SmackOptions::BitPrecise &&
    (SmackOptions::NoByteAccessInference || !aliasAnalysis->isFieldDisjoint(V,offset));
}

bool SmackRep::bytewiseAccess(const Value* V, const Function* F) {
  return SmackOptions::BitPrecise &&
    (SmackOptions::NoByteAccessInference || !aliasAnalysis->isFieldDisjoint(V,F));
}

string SmackRep::memType(unsigned region, unsigned size) {
  stringstream s;
  if (!memoryRegions[region].isSingletonGlobal || (SmackOptions::BitPrecise && SmackOptions::NoByteAccessInference))
    s << "[" << PTR_TYPE << "] ";
  s << intType(size);
  return s.str();
}

string SmackRep::memPath(unsigned region, unsigned size) {
  if (SmackOptions::BitPrecise)
    return (memReg(region) + "." + intType(size));
  else
    return memReg(region);
}

const Expr* SmackRep::mem(const llvm::Value* v) {
  return mem(getRegion(v), expr(v), getElementSize(v));
}

const Expr* SmackRep::mem(unsigned region, const Expr* addr, unsigned size) {
  if (memoryRegions[region].isSingletonGlobal)
    return Expr::id(memPath(region, size));
  else
    return Expr::sel(Expr::id(memPath(region, size)), addr);
}

unsigned SmackRep::getRegion(const llvm::Value* v) {
  unsigned r;

  for (r=0; r<memoryRegions.size(); ++r)
    if (!aliasAnalysis->isNoAlias(v, memoryRegions[r].representative))
      break;

  if (r == memoryRegions.size()) {
    llvm::Type* T = v->getType();
    while (T->isPointerTy()) T = T->getPointerElementType();
    memoryRegions.emplace_back(v,false,
      aliasAnalysis->isSingletonGlobal(v) && T->isSingleValueType()
    );
  }

  memoryRegions[r].isAllocated = memoryRegions[r].isAllocated || aliasAnalysis->isAlloced(v);
  return r;
}

bool SmackRep::isExternal(const llvm::Value* v) {
  return v->getType()->isPointerTy() && !memoryRegions[getRegion(v)].isAllocated;
}

void SmackRep::collectRegions(llvm::Module &M) {
  RegionCollector rc(*this);
  rc.visit(M);
}

const Stmt* SmackRep::alloca(llvm::AllocaInst& i) {
  const Expr* size =
    Expr::fn("$mul.ref",
      pointerLit(storageSize(i.getAllocatedType())),
      pointerLit((unsigned long) llvm::cast<llvm::ConstantInt>(i.getArraySize())->getZExtValue()));

  // TODO this should not be a pointer type.
  return Stmt::call("$alloc",{size},{naming.get(i)});
}

const Stmt* SmackRep::memcpy(const llvm::MemCpyInst& mci) {
  vector<const Expr*> args;
  unsigned r1 = getRegion(mci.getOperand(0));
  unsigned r2 = getRegion(mci.getOperand(1));
  for (unsigned i = 0; i < mci.getNumArgOperands(); i++)
    args.push_back(expr(mci.getOperand(i)));
  return Stmt::call(indexedName(naming.get(*mci.getCalledFunction()), {r1,r2}), args);
}

const Stmt* SmackRep::memset(const llvm::MemSetInst& msi) {
  vector<const Expr*> args;
  unsigned r = getRegion(msi.getOperand(0));
  for (unsigned i = 0; i < msi.getNumArgOperands(); i++)
    args.push_back(expr(msi.getOperand(i)));
  return Stmt::call(indexedName(naming.get(*msi.getCalledFunction()), {r}), args);
}

const Stmt* SmackRep::load(const llvm::LoadInst& LI) {
  const llvm::Value* P = LI.getPointerOperand();
  const unsigned size = getElementSize(P);
  const Expr* rhs;

  if (bytewiseAccess(P, LI.getParent()->getParent())) {
    stringstream name;
    name << "$load." << intType(size);
    rhs = Expr::fn(name.str(), Expr::id(memPath(getRegion(P), 8)), expr(P));

  } else
    rhs = mem(P);

  if (isFloat(&LI))
    rhs = Expr::fn(opName("$si2fp", {size}), rhs);

  else if (LI.getType()->isPointerTy())
    rhs = integerToPointer(rhs, size);

  return Stmt::assign(expr(&LI), rhs);
}

const Stmt* SmackRep::store(const llvm::StoreInst& SI) {
  const llvm::Value* P = SI.getPointerOperand();
  const llvm::Value* V = SI.getOperand(0);
  const unsigned size = getElementSize(P);

  return store(getRegion(P), size, expr(P), V, bytewiseAccess(P, SI.getParent()->getParent()));
}

const Stmt* SmackRep::store(unsigned region, unsigned size, const Expr* addr, const llvm::Value* val, bool bytewise) {
  const Expr* rhs = expr(val);

  if (val->getType()->isFloatingPointTy())
    rhs = Expr::fn(opName("$fp2si",{val->getType(), llvm::IntegerType::get(val->getContext(),size)}), rhs);

  else if (val->getType()->isPointerTy())
    rhs = pointerToInteger(rhs, size);

  if (bytewise)
    return Stmt::assign(
      Expr::id(memPath(region, 8)),
      Expr::fn("$store." + intType(size), Expr::id(memPath(region,8)), addr, rhs)
    );
  else
    return Stmt::assign(mem(region, addr, size), rhs);
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
    return Expr::id(NULL_VAL);

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
      return Expr::id(NULL_VAL);

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
  return Expr::fn(opName(INSTRUCTION_TABLE.at(opcode), {v->getType(), t}), expr(v));
}

const Expr* SmackRep::bop(const llvm::ConstantExpr* CE) {
  return bop(CE->getOpcode(), CE->getOperand(0), CE->getOperand(1), CE->getType());
}

const Expr* SmackRep::bop(const llvm::BinaryOperator* BO) {
  return bop(BO->getOpcode(), BO->getOperand(0), BO->getOperand(1), BO->getType());
}

const Expr* SmackRep::bop(unsigned opcode, const llvm::Value* lhs, const llvm::Value* rhs, const llvm::Type* t) {
  string fn = INSTRUCTION_TABLE.at(opcode);
  return Expr::fn(opName(fn, {t}), expr(lhs), expr(rhs));
}

const Expr* SmackRep::cmp(const llvm::CmpInst* I) {
  return cmp(I->getPredicate(), I->getOperand(0), I->getOperand(1));
}

const Expr* SmackRep::cmp(const llvm::ConstantExpr* CE) {
  return cmp(CE->getPredicate(), CE->getOperand(0), CE->getOperand(1));
}

const Expr* SmackRep::cmp(unsigned predicate, const llvm::Value* lhs, const llvm::Value* rhs) {
  string fn = CMPINST_TABLE.at(predicate);
  return Expr::fn(opName(fn, {lhs->getType()}), expr(lhs), expr(rhs));
}

vector<Decl*> SmackRep::decl(llvm::Function* F) {
  vector<Decl*> decls;
  string name = naming.get(*F);

  for (llvm::Value::user_iterator U = F->user_begin(); U != F->user_end(); ++U)
    if (MemCpyInst* MCI = dyn_cast<MemCpyInst>(*U)) {
      llvm::FunctionType* T = F->getFunctionType();
      llvm::Type
        *dst = T->getParamType(0),
        *src = T->getParamType(1),
        *len = T->getParamType(2),
        *align = T->getParamType(3),
        *vol  = T->getParamType(4);
      unsigned r1 = getRegion(MCI->getOperand(0));
      unsigned r2 = getRegion(MCI->getOperand(1));

      decls.push_back(Decl::procedure(program, indexedName(name,{r1,r2}), {
        {"dst", type(dst)},
        {"src", type(src)},
        {"len", type(len)},
        {"align", type(align)},
        {"volatile", type(vol)},
      }, {}, {
        Block::block("", {
          Stmt::call(indexedName("$memcpy",{r1,r2}), {
            Expr::id("dst"),
            Expr::id("src"),
            integerToPointer(Expr::id("len"), len->getIntegerBitWidth()),
            integerToPointer(Expr::id("align"), align->getIntegerBitWidth()),
            Expr::eq(Expr::id("volatile"), integerLit(1UL,1))
          })
        })
      }));
      decls.push_back(memcpyProc(r1,r2));

    } else if (MemSetInst* MSI = dyn_cast<MemSetInst>(*U)) {
      llvm::FunctionType* T = F->getFunctionType();
      llvm::Type
        *dst = T->getParamType(0),
        *val = T->getParamType(1),
        *len = T->getParamType(2),
        *align = T->getParamType(3),
        *vol  = T->getParamType(4);
      unsigned r = getRegion(MSI->getOperand(0));

      decls.push_back(Decl::procedure(program, indexedName(name,{r}), {
        {"dst", type(dst)},
        {"val", type(val)},
        {"len", type(len)},
        {"align", type(align)},
        {"volatile", type(vol)},
      }, {}, {
        Block::block("", {
          Stmt::call(indexedName("$memset",{r}), {
            Expr::id("dst"),
            Expr::id("val"),
            integerToPointer(Expr::id("len"), len->getIntegerBitWidth()),
            integerToPointer(Expr::id("align"), align->getIntegerBitWidth()),
            Expr::eq(Expr::id("volatile"), integerLit(1UL,1))
          })
        })
      }));
      decls.push_back(memsetProc(r));

    } else if (name == "malloc") {
      llvm::Type* T = F->getFunctionType()->getParamType(0);
      assert (T->isIntegerTy() && "Expected integer argument.");
      unsigned width = T->getIntegerBitWidth();
      decls.push_back(Decl::procedure(program, name, {{"n", type(T)}}, {{"r", PTR_TYPE}}, {
        Block::block("", { Stmt::call("$alloc", {integerToPointer(Expr::id("n"),width)}, {"r"}) })
      }));

    } else if (name == "free_") {
      decls.push_back(Decl::procedure(program, name, {{"n", PTR_TYPE}}, {}, {
        Block::block("", { Stmt::call("$free", {Expr::id("n")}) })
      }));

    } else {
      Naming N;
      vector< pair<string,string> > params, rets;
      for (unsigned i = 0; i < U->getNumOperands()-1; i++) {
        const llvm::Value* V = U->getOperand(i);
        params.push_back({N.freshVarName(*V),type(V->getType())});
      }
      if (!F->getReturnType()->isVoidTy())
        rets.push_back({"r", type(F->getReturnType())});
      decls.push_back(Decl::procedure(program, procName(**U,F), params, rets));
    }

  return decls;
}

ProcDecl* SmackRep::proc(llvm::Function* f) {
  vector< pair<string,string> > parameters, returns;

  unsigned i = 0;
  for (llvm::Function::arg_iterator
       arg = f->arg_begin(), e = f->arg_end(); arg != e; ++arg, ++i) {
    string name;
    if (arg->hasName()) {
      name = naming.get(*arg);
    } else {
      name = indexedName("p",{i});
      arg->setName(name);
    }

    parameters.push_back({name, type(arg->getType())});
  }

  if (!f->getReturnType()->isVoidTy())
    returns.push_back({Naming::RET_VAR,type(f->getReturnType())});

  return (ProcDecl*) Decl::procedure(
    program,
    f->isVarArg() ? naming.get(*f) : naming.get(*f),
    parameters,
    returns
  );
}

const Expr* SmackRep::arg(llvm::Function* f, unsigned pos, llvm::Value* v) {
  return (f && f->isVarArg() && isFloat(v))
    ? Expr::fn(opName("$fp2si", {f->getType(), v->getType()}), expr(v))
    : expr(v);
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
  assert(!fmt.empty() && "__SMACK_code: missing format string.");

  string s = fmt;
  for (unsigned i=1; i<ci.getNumOperands()-1; i++) {
    const Expr* a = arg(f, i, ci.getOperand(i));
    string::size_type idx = s.find('@');
    assert(idx != string::npos && "__SMACK_code: too many arguments.");

    ostringstream ss;
    a->print(ss);
    s = s.replace(idx,1,ss.str());
  }
  return s;
}

string SmackRep::getPrelude() {
  stringstream s;

  s << "// Basic types" << endl;
  for (auto t : {"i1", "i8", "i16", "i32", "i64", "i96", "i128"})
    s << Decl::typee(t,"int") << endl;
  s << Decl::typee(PTR_TYPE, pointerType()) << endl;
  s << endl;

  s << "// Basic constants" << endl;
  s << Decl::constant("$0",intType(32)) << endl;
  s << Decl::axiom(Expr::eq(Expr::id("$0"),integerLit(0UL,32))) << endl;

  for (int i=0; i<15; i++)
    s << "const $" << i << ".ref: ref;" << endl;

  for (unsigned i = 0; i < 8; ++i) {
    stringstream t;
    t << "$" << i << ".ref";
    s << Decl::axiom(Expr::eq(Expr::id(t.str()),pointerLit((unsigned long) i))) << endl;
  }
  s << endl;

  s << "// Memory maps (" << memoryRegions.size() << " regions)" << endl;
  for (unsigned i=0; i<memoryRegions.size(); ++i) {
    unsigned n = uniformMemoryAccesses() ? 1 : 4;
    for (unsigned j = 0; j < n; j++) {
      unsigned size = 8 << j;
      s << "var " << memPath(i, size)
        << ": " << memType(i, size)
        << ";" << endl;
    }
  }
  s << endl;

  s << "// Memory address bounds" << endl;
  s << Decl::axiom(Expr::eq(Expr::id(GLOBALS_BOTTOM),pointerLit(globalsBottom))) << endl;
  s << Decl::axiom(Expr::eq(Expr::id(EXTERNS_BOTTOM),pointerLit(externsBottom))) << endl;
  s << Decl::axiom(Expr::eq(Expr::id(MALLOC_TOP),pointerLit((unsigned long) INT_MAX - 10485760))) << endl;
  s << endl;

  s << "// Bitvector-integer conversions" << endl;
  string b = to_string(ptrSizeInBits);
  string bt = "bv" + b;
  string it = "i" + b;
  s << Decl::function(indexedName("$bv2int",{ptrSizeInBits}), {{"i",bt}}, it, NULL, {Attr::attr("builtin", "bv2int")}) << endl;
  s << Decl::function(indexedName("$int2bv",{ptrSizeInBits}), {{"i",it}}, bt, NULL, {Attr::attr("builtin", "(_ int2bv " + b + ")")}) << endl;
  s << endl;

  s << "// Pointer-number conversions" << endl;
  for (unsigned i = 8; i <= 64; i <<= 1) {
    s << Decl::function(indexedName("$p2i", {PTR_TYPE,intType(i)}), {{"p",PTR_TYPE}}, intType(i), pointerToInteger(Expr::id("p"),i), {Attr::attr("inline")}) << endl;
    s << Decl::function(indexedName("$i2p", {intType(i),PTR_TYPE}), {{"i",intType(i)}}, PTR_TYPE, integerToPointer(Expr::id("i"),i), {Attr::attr("inline")}) << endl;
  }
  s << endl;

  s << "// Pointer predicates" << endl;
  const vector<string> predicates {"$eq", "$ne", "$sge", "$sgt", "$sle", "$slt"};
  for (auto pred : predicates) {
    s << Decl::function(indexedName(pred,{PTR_TYPE}),
      {{"p1",PTR_TYPE}, {"p2",PTR_TYPE}}, intType(1),
      Expr::cond(
        Expr::fn(indexedName(pred,{pointerType(),BOOL_TYPE}), {Expr::id("p1"),Expr::id("p2")}),
        integerLit(1L,1),
        integerLit(0L,1)),
      {Attr::attr("inline")} )
      << endl;
    s << Decl::function(indexedName(pred,{PTR_TYPE,BOOL_TYPE}),
      {{"p1",PTR_TYPE}, {"p2",PTR_TYPE}}, BOOL_TYPE,
      Expr::fn(indexedName(pred,{pointerType(),BOOL_TYPE}), {Expr::id("p1"),Expr::id("p2")}),
      {Attr::attr("inline")} )
      << endl;
  }
  s << endl;

  s << "// Pointer operations" << endl;
  const vector<string> operations = {"$add", "$sub", "$mul"};
  for (auto op : operations) {
    s << Decl::function(indexedName(op,{PTR_TYPE}),
      {{"p1",PTR_TYPE},{"p2",PTR_TYPE}}, PTR_TYPE,
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

vector<string> SmackRep::getModifies() {
  vector<string> mods;
  for (vector<string>::iterator i = bplGlobals.begin(); i != bplGlobals.end(); ++i)
    mods.push_back(*i);
  for (unsigned i=0; i<memoryRegions.size(); ++i) {
    unsigned n = uniformMemoryAccesses() ? 1 : 4;
    for (unsigned j=0; j < n; ++j) {
      unsigned size = 8 << j;
      mods.push_back(memPath(i, size));
    }
  }
  return mods;
}

unsigned SmackRep::numElements(const llvm::Constant* v) {
  using namespace llvm;
  if (const ArrayType* at = dyn_cast<const ArrayType>(v->getType()))
    return at->getNumElements();
  else
    return 1;
}

void SmackRep::addInit(const llvm::GlobalValue* G, const llvm::Constant* C) {
  addInit(G, expr(G), C, bytewiseAccess(G,0));
}

void SmackRep::addInit(const llvm::GlobalValue* G, const Expr* addr, const llvm::Constant* C, bool bytewise) {
  using namespace llvm;

  if (C->getType()->isIntegerTy() ||
      C->getType()->isPointerTy() ||
      C->getType()->isFloatingPointTy()) {
    staticInits.push_back(store(getRegion(G), getSize(C->getType()), addr, C, bytewise));

  } else if (ArrayType* at = dyn_cast<ArrayType>(C->getType())) {
    for (unsigned i = 0; i < at->getNumElements(); i++) {

      // TODO shouldn’t we be accummulating the offset from G?
      addInit(G, pa(addr,i,storageSize(at->getElementType())), C->getAggregateElement(i),
        bytewiseAccess(G, offset(at,i)));
    }

  } else if (StructType* st = dyn_cast<StructType>(C->getType())) {
    for (unsigned i = 0; i < st->getNumElements(); i++) {

      // TODO shouldn’t we be accummulating the offset from G?
      addInit(G, pa(addr,offset(st,i),1), C->getAggregateElement(i),
        bytewiseAccess(G, offset(st,i)));
    }

  } else if (C->getType()->isX86_FP80Ty()) {
    staticInits.push_back(Stmt::code("// ignored X86 FP80 initializer"));

  } else {
    assert (false && "Unexpected static initializer.");
  }
}

void SmackRep::addInitFunc(const llvm::Function* f) {
  assert(f->getReturnType()->isVoidTy() && "Init functions cannot return a value");
  assert(f->getArgumentList().empty() && "Init functions cannot take parameters");
  initFuncs.push_back(Stmt::call(naming.get(*f)));
}

Decl* SmackRep::getStaticInit() {
  ProcDecl* proc = (ProcDecl*) Decl::procedure(program, STATIC_INIT);
  Block* b = Block::block();

  b->addStmt(Stmt::assign(Expr::id("$CurrAddr"), pointerLit(1024UL)));
  for (unsigned i=0; i<staticInits.size(); i++)
    b->addStmt(staticInits[i]);
  b->addStmt(Stmt::return_());
  proc->addBlock(b);
  return proc;
}

Decl* SmackRep::getInitFuncs() {
  ProcDecl* proc = (ProcDecl*) Decl::procedure(program, INIT_FUNCS);
  Block* b = Block::block();

  for (unsigned i=0; i<initFuncs.size(); i++)
    b->addStmt(initFuncs[i]);
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

        addInit(g, init);
      }

    } else {
      external = true;
    }
  }

  decls.push_back(Decl::constant(name, PTR_TYPE, ax, false));

  if (!size)
    size = targetData->getPrefTypeAlignment(v->getType());

  decls.push_back(Decl::axiom(Expr::eq(
    Expr::id(name),
    pointerLit(external ? externsBottom -= size : globalsBottom -= size) )));

  return decls;
}

const Expr* SmackRep::declareIsExternal(const Expr* e) {
  return Expr::fn("$isExternal",e);
}

Decl* SmackRep::memcpyProc(unsigned dstReg, unsigned srcReg) {
  stringstream s;
  unsigned n = uniformMemoryAccesses() ? 1 : 4;

  s << "procedure $memcpy." << dstReg << "." << srcReg;
  s << "(dest: ref, src: ref, len: ref, align: ref, isvolatile: bool)";
  s << (SmackOptions::MemoryModelImpls ? "" : ";") << endl;

  for (unsigned i = 0; i < n; ++i)
    s << "modifies " << memPath(dstReg, 8 << i) << ";" << endl;

  if (SmackOptions::MemoryModelImpls) {
    s << "{" << endl;
    for (unsigned i = 0; i < n; ++i) {
      unsigned size = 8 << i;
      s << "  var $oldSrc" << ".i" << size << " : [" << PTR_TYPE << "] " << intType(size) << ";" << endl;
      s << "  var $oldDst" << ".i" << size << " : [" << PTR_TYPE << "] " << intType(size) << ";" << endl;
    }
    for (unsigned i = 0; i < n; ++i) {
      unsigned size = 8 << i;
      s << "  $oldSrc" << ".i" << size << " := " << memPath(srcReg, size) << ";" << endl;
      s << "  $oldDst" << ".i" << size << " := " << memPath(dstReg, size) << ";" << endl;
      s << "  havoc " << memPath(dstReg, size) << ";" << endl;
      s << "  assume (forall x:ref :: $sle.ref.bool(dest, x) && $slt.ref.bool(x, $add.ref(dest, len)) ==> "
        << memPath(dstReg, size) << "[x] == $oldSrc" << ".i" << size << "[$add.ref($sub.ref(src, dest), x)]);" << endl;
      s << "  assume (forall x:ref :: !($sle.ref.bool(dest, x) && $slt.ref.bool(x, $add.ref(dest, len))) ==> "
        << memPath(dstReg, size) << "[x] == $oldDst" << ".i" << size << "[x]);" << endl;
    }
    s << "}" << endl;
  } else {
    for (unsigned i = 0; i < n; ++i) {
      unsigned size = 8 << i;
      s << "ensures (forall x:ref :: $sle.ref.bool(dest, x) && $slt.ref.bool(x, $add.ref(dest, len)) ==> "
        << memPath(dstReg, size) << "[x] == old(" << memPath(srcReg, size) << ")[$add.ref($sub.ref(src, dest), x)]);"
        << endl;
      s << "ensures (forall x:ref :: !($sle.ref.bool(dest, x) && $slt.ref.bool(x, $add.ref(dest, len))) ==> "
        << memPath(dstReg, size) << "[x] == old(" << memPath(dstReg, size) << ")[x]);" << endl;
    }
  }

  return Decl::code(s.str());
}

Decl* SmackRep::memsetProc(unsigned dstReg) {
  stringstream s;
  unsigned n = uniformMemoryAccesses() ? 1 : 4;

  s << "procedure $memset." << dstReg;
  s << "(dest: ref, val: " << intType(8) << ", len: ref, align: ref, isvolatile: bool)";
  s << (SmackOptions::MemoryModelImpls ? "" : ";") << endl;

  for (unsigned i = 0; i < n; ++i)
    s << "modifies " << memPath(dstReg, 8 << i) << ";" << endl;

  if (SmackOptions::MemoryModelImpls) {
    s << "{" << endl;
    for (unsigned i = 0; i < n; ++i) {
      unsigned size = 8 << i;
      s << "  var $oldDst" << ".i" << size << " : [" << PTR_TYPE << "] " << intType(size) << ";" << endl;
    }

    string val = "val";
    for (unsigned i = 0; i < n; ++i) {
      unsigned size = 8 << i;
      s << "  $oldDst" << ".i" << size << " := " << memPath(dstReg, size) << ";" << endl;
      s << "  havoc " << memPath(dstReg, size) << ";" << endl;
      s << "  assume (forall x:ref :: $sle.ref.bool(dest, x) && $slt.ref.bool(x, $add.ref(dest, len)) ==> "
        << memPath(dstReg, size) << "[x] == "
        << val
        << ");" << endl;
      s << "  assume (forall x:ref :: !($sle.ref.bool(dest, x) && $slt.ref.bool(x, $add.ref(dest, len))) ==> "
        << memPath(dstReg, size) << "[x] == $oldDst" << ".i" << size << "[x]);" << endl;
      val = val + "++" + val;
    }
    s << "}" << endl;
  } else {
    string val = "val";
    for (unsigned i = 0; i < n; ++i) {
      unsigned size = 8 << i;
      s << "ensures (forall x:ref :: $sle.ref.bool(dest, x) && $slt.ref.bool(x, $add.ref(dest, len)) ==> "
        << memPath(dstReg, size) << "[x] == "
        << val
        << ");" << endl;
      s << "ensures (forall x:ref :: !($sle.ref.bool(dest, x) && $slt.ref.bool(x, $add.ref(dest, len))) ==> "
        << memPath(dstReg, size) << "[x] == old(" << memPath(dstReg, size) << ")[x]);" << endl;
      val = val + "++" + val;
    }
  }

  return Decl::code(s.str());
}

} // namespace smack
