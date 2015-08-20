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

const vector<unsigned> INTEGER_SIZES = {1, 8, 16, 32, 64, 96, 128};

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

void SmackRep::print(raw_ostream &O) {
  O << "";
  for (auto & R : memoryRegions) {
    O << "XXX Region(";
    R.print(O);
    O << ")\n";
  }
  O << "\n";
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

vector<unsigned> SmackRep::memoryAccessSizes() {
  if (!SmackOptions::BitPrecise)
    return {std::numeric_limits<unsigned>::max()};
  else if (SmackOptions::NoByteAccessInference)
    return {8};
  else
    return {8, 16, 32, 64, 96, 128};
}

string SmackRep::memType(unsigned region, unsigned size) {
  stringstream s;
  if (!memoryRegions[region].isSingleton() ||
      (SmackOptions::BitPrecise && SmackOptions::NoByteAccessInference))
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

unsigned SmackRep::getRegion(const llvm::Value* V) {
  DEBUG(errs() << "XXX getRegion(" << *V << ")");
  Region R(V);
  return getRegion(R);
}

unsigned SmackRep::getRegion(const Value* V, unsigned length) {
  DEBUG(errs() << "XXX getRegion[" << length << "](" << *V << ")");
  Region R(V,length);
  return getRegion(R);
}

unsigned SmackRep::getRegion(const llvm::Value* V,
    unsigned offset, unsigned length) {
  DEBUG(errs() << "XXX getRegion[" << offset << "," << length << "](" << *V << ")");
  Region R(V,offset,length);
  return getRegion(R);
}

unsigned SmackRep::getRegion(Region& R) {
  unsigned r;

  for (r = 0; r < memoryRegions.size(); ++r) {
    if (memoryRegions[r].overlaps(R)) {
      memoryRegions[r].merge(R);
      break;
    }
  }

  if (r == memoryRegions.size())
    memoryRegions.emplace_back(R);

  else {
    // Here is the tricky part: in case R was merged with an existing region,
    // we must now also merge any other region which intersects with R.
    unsigned q = r+1;
    while (q < memoryRegions.size()) {
      if (memoryRegions[r].overlaps(memoryRegions[q])) {
        memoryRegions[r].merge(memoryRegions[q]);
        memoryRegions.erase(memoryRegions.begin()+q);
      } else {
        q++;
      }
    }
  }

  DEBUG(errs() << " => " << r << "\n");

  return r;
}

bool SmackRep::isExternal(const llvm::Value* v) {
  return v->getType()->isPointerTy()
      && !memoryRegions[getRegion(v)].isAllocated();
}

void SmackRep::collectRegions(llvm::Module &M) {
  RegionCollector RC(
    [this](const Value* V){ getRegion(V); },
    [this](const Value* V, unsigned len){ getRegion(V,len); });
  RC.visit(M);
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
  unsigned length = dyn_cast<ConstantInt>(mci.getLength())->getZExtValue();
  unsigned r1 = getRegion(mci.getOperand(0),length);
  unsigned r2 = getRegion(mci.getOperand(1),length);
  for (unsigned i = 0; i < mci.getNumArgOperands(); i++)
    args.push_back(expr(mci.getOperand(i)));
  return Stmt::call(indexedName(naming.get(*mci.getCalledFunction()), {r1,r2}), args);
}

const Stmt* SmackRep::memset(const llvm::MemSetInst& msi) {
  vector<const Expr*> args;
  unsigned length = dyn_cast<ConstantInt>(msi.getLength())->getZExtValue();
  unsigned r = getRegion(msi.getOperand(0),length);
  for (unsigned i = 0; i < msi.getNumArgOperands(); i++)
    args.push_back(expr(msi.getOperand(i)));
  return Stmt::call(indexedName(naming.get(*msi.getCalledFunction()), {r}), args);
}

const Expr* SmackRep::load(const llvm::Value* P) {
  const PointerType* T = dyn_cast<PointerType>(P->getType());
  assert(T && "Expected pointer type.");
  const unsigned R = getRegion(P);
  const unsigned size = getElementSize(P);
  bool bytewise = memoryRegions[R].bytewiseAccess();
  bool singleton = memoryRegions[R].isSingleton();
  const Expr* M = Expr::id(memPath(R, bytewise ? 8 : size));
  string N = string("$load.") + (bytewise ? "bytes." : "") + intType(size);
  const Expr* expr = singleton ? M : Expr::fn(N, M, SmackRep::expr(P));

  if (T->getElementType()->isFloatingPointTy())
    expr = Expr::fn(opName("$si2fp",
      {IntegerType::get(P->getContext(),size), T->getElementType()}), expr);

  else if (T->getElementType()->isPointerTy())
    expr = integerToPointer(expr, size);

  return expr;
}

const Stmt* SmackRep::store(const Value* P, const Value* V) {
  return store(P, expr(V));
}

const Stmt* SmackRep::store(const Value* P, const Expr* V) {
  const PointerType* T = dyn_cast<PointerType>(P->getType());
  assert(T && "Expected pointer type.");
  return store(getRegion(P), T->getElementType(), expr(P), V);
}

const Stmt* SmackRep::store(const GlobalValue* G, unsigned offset,
    const Value* V) {
  return store(
    getRegion(G, offset, targetData->getTypeStoreSize(V->getType())),
    V->getType(),
    pa(expr(G), 1, offset),
    expr(V));
}

const Stmt* SmackRep::store(unsigned R, const Type* T,
    const Expr* P, const Expr* V) {
  unsigned size = targetData->getTypeStoreSizeInBits((Type*) T);
  bool bytewise = memoryRegions[R].bytewiseAccess();
  bool singleton = memoryRegions[R].isSingleton();
  string N = string("$store.") + (bytewise ? "bytes." : "") + intType(size);
  const Expr* M = Expr::id(memPath(R, bytewise ? 8 : size));
  if (T->isFloatingPointTy())
    V = Expr::fn(opName("$fp2si",
      {T, llvm::IntegerType::get(T->getContext(),size)}), V);
  else if (T->isPointerTy())
    V = pointerToInteger(V, size);
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

    if (MemCpyInst* MCI = dyn_cast<MemCpyInst>(U)) {
      llvm::FunctionType* T = F->getFunctionType();
      llvm::Type
        *dst = T->getParamType(0),
        *src = T->getParamType(1),
        *len = T->getParamType(2),
        *align = T->getParamType(3),
        *vol  = T->getParamType(4);
      unsigned length = dyn_cast<ConstantInt>(MCI->getLength())->getZExtValue();
      unsigned r1 = getRegion(MCI->getOperand(0),length);
      unsigned r2 = getRegion(MCI->getOperand(1),length);

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

    } else if (MemSetInst* MSI = dyn_cast<MemSetInst>(U)) {
      llvm::FunctionType* T = F->getFunctionType();
      llvm::Type
        *dst = T->getParamType(0),
        *val = T->getParamType(1),
        *len = T->getParamType(2),
        *align = T->getParamType(3),
        *vol  = T->getParamType(4);
      unsigned length = dyn_cast<ConstantInt>(MSI->getLength())->getZExtValue();
      unsigned r = getRegion(MSI->getOperand(0),length);

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
  for (unsigned size : INTEGER_SIZES)
    s << Decl::typee("i" + std::to_string(size),"int") << endl;
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
    for (unsigned size : memoryAccessSizes())
      s << "var " << memPath(i, size)
        << ": " << memType(i, size)
        << ";" << endl;
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
  const vector<string> predicates {
    "$eq", "$ne", "$ugt", "$uge", "$ult", "$ule", "$sgt", "$sge", "$slt", "$sle"
  };
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
    for (unsigned size : memoryAccessSizes())
      mods.push_back(memPath(i, size));
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
  addInit(G, 0, C);
}

void SmackRep::addInit(const llvm::GlobalValue* G, unsigned offset,
    const llvm::Constant* C) {

  if (C->getType()->isIntegerTy() ||
      C->getType()->isPointerTy() ||
      C->getType()->isFloatingPointTy()) {
    staticInits.push_back(store(G, offset, C));

  } else if (ArrayType* at = dyn_cast<ArrayType>(C->getType()))
    for (unsigned i = 0; i < at->getNumElements(); i++)
      addInit(G, offset + SmackRep::offset(at,i), C->getAggregateElement(i));

  else if (StructType* st = dyn_cast<StructType>(C->getType()))
    for (unsigned i = 0; i < st->getNumElements(); i++)
      addInit(G, offset + SmackRep::offset(st,i), C->getAggregateElement(i));

  else if (C->getType()->isX86_FP80Ty()) {
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

  s << "procedure $memcpy." << dstReg << "." << srcReg;
  s << "(dest: ref, src: ref, len: ref, align: ref, isvolatile: bool)";
  s << (SmackOptions::MemoryModelImpls ? "" : ";") << endl;

  for (unsigned size : memoryAccessSizes())
    s << "modifies " << memPath(dstReg, size) << ";" << endl;

  if (SmackOptions::MemoryModelImpls) {
    s << "{" << endl;
    for (unsigned size : memoryAccessSizes()) {
      s << "  var $oldSrc" << ".i" << size << " : [" << PTR_TYPE << "] " << intType(size) << ";" << endl;
      s << "  var $oldDst" << ".i" << size << " : [" << PTR_TYPE << "] " << intType(size) << ";" << endl;
    }
    for (unsigned size : memoryAccessSizes()) {
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
    for (unsigned size : memoryAccessSizes()) {
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

  s << "procedure $memset." << dstReg;
  s << "(dest: ref, val: " << intType(8) << ", len: ref, align: ref, isvolatile: bool)";
  s << (SmackOptions::MemoryModelImpls ? "" : ";") << endl;

  for (unsigned size : memoryAccessSizes())
    s << "modifies " << memPath(dstReg, size) << ";" << endl;

  if (SmackOptions::MemoryModelImpls) {
    s << "{" << endl;
    for (unsigned size : memoryAccessSizes())
      s << "  var $oldDst" << ".i" << size << " : [" << PTR_TYPE << "] " << intType(size) << ";" << endl;

    for (unsigned size : memoryAccessSizes()) {
      s << "  $oldDst" << ".i" << size << " := " << memPath(dstReg, size) << ";" << endl;
      s << "  havoc " << memPath(dstReg, size) << ";" << endl;
      s << "  assume (forall x:ref :: $sle.ref.bool(dest, x) && $slt.ref.bool(x, $add.ref(dest, len)) ==> ";
      s << memPath(dstReg, size) << "[x] == val";
      if (size != std::numeric_limits<unsigned>::max())
        for (unsigned i = 8; i < size; i += 8)
          s << " ++ val";
      s << ");" << endl;
      s << "  assume (forall x:ref :: !($sle.ref.bool(dest, x) && $slt.ref.bool(x, $add.ref(dest, len))) ==> ";
      s << memPath(dstReg, size) << "[x] == $oldDst" << ".i" << size << "[x]);" << endl;
    }
    s << "}" << endl;
  } else {
    for (unsigned size : memoryAccessSizes()) {
      s << "ensures (forall x:ref :: $sle.ref.bool(dest, x) && $slt.ref.bool(x, $add.ref(dest, len)) ==> ";
      s << memPath(dstReg, size) << "[x] == val";
      if (size != std::numeric_limits<unsigned>::max())
        for (unsigned i = 8; i < size; i += 8)
          s << " ++ val";
      s << ");" << endl;
      s << "ensures (forall x:ref :: !($sle.ref.bool(dest, x) && $slt.ref.bool(x, $add.ref(dest, len))) ==> ";
      s << memPath(dstReg, size) << "[x] == old(" << memPath(dstReg, size) << ")[x]);" << endl;
    }
  }

  return Decl::code(s.str());
}

} // namespace smack
