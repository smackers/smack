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

const string SmackRep::NEG = "$neg";

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

bool SmackRep::isMallocOrFree(const llvm::Function* f) {
  return PROC_MALLOC_FREE.match(naming.get(*f));
}

bool SmackRep::isIgnore(const llvm::Function* f) {
  return PROC_IGNORE.match(naming.get(*f));
}

bool SmackRep::isInt(const llvm::Type* t) {
  return t->isIntegerTy();
}

bool SmackRep::isInt(const llvm::Value* v) {
  return isInt(v->getType());
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

bool SmackRep::isFloat(const llvm::Type* t) {
  return t->isFloatingPointTy();
}

bool SmackRep::isFloat(const llvm::Value* v) {
  return isFloat(v->getType());
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

unsigned SmackRep::storageSize(llvm::Type* t) {
  return targetData->getTypeStoreSize(t);
}

unsigned SmackRep::fieldOffset(llvm::StructType* t, unsigned fieldNo) {
  return targetData->getStructLayout(t)->getElementOffset(fieldNo);
}

string SmackRep::memReg(unsigned idx) {
  stringstream s;
  s << "$M." << idx;
  return s.str();
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
  unsigned r = getRegion(v);
  return mem(r, expr(v), getElementSize(v));
}

const Expr* SmackRep::mem(unsigned region, const Expr* addr, unsigned size) {
  if (memoryRegions[region].isSingletonGlobal)
    return Expr::id(memPath(region, size));
  else
    return Expr::sel(Expr::id(memPath(region, size)),addr);
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

string SmackRep::name(const llvm::Function* F, initializer_list<unsigned> regions) {
  stringstream name;
  name << naming.get(*F);

  // if (F->isVarArg()) {
  //   for (unsigned i = 0; i < U.getNumOperands()-1; i++)
  //     name << "." << type(U.getOperand(i)->getType());
  // }

  for (auto r : regions)
    name << "." << r;

  return name.str();
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

const Stmt* SmackRep::load(const llvm::Value* addr, const llvm::Value* val) {
// The tricky part is that we could expr(li) is actually expr(val) so that it is possible to pass li to val. 
  const Expr* rhs;

  if (!SmackOptions::BitPrecise || (!SmackOptions::NoByteAccessInference && isFieldDisjoint(addr, llvm::cast<const llvm::Instruction>(val))))
    rhs = mem(addr);
  else {
    stringstream name;
    name << "$load." << intType(getElementSize(addr));
    rhs = Expr::fn(name.str(), Expr::id(memPath(getRegion(addr), 8)), expr(addr));
  }

  if (isFloat(val))
    rhs = Expr::fn(opName("$si2fp", {getElementSize(addr)}), rhs);
  
  return Stmt::assign(expr(val), rhs);
}

const Stmt* SmackRep::store(const llvm::Value* addr, const llvm::Value* val, const llvm::StoreInst* si) {
// Having a default value of si (NULL) is unsound.
  const Expr* rhs = expr(val);

  if (isFloat(val))
    rhs = Expr::fn(opName("$fp2si", {getElementSize(addr)}), rhs);

  if (!SmackOptions::BitPrecise || (!SmackOptions::NoByteAccessInference && isFieldDisjoint(addr, si)))
    return Stmt::assign(mem(addr),rhs);
  else
    return storeAsBytes(getRegion(addr), getElementSize(addr), expr(addr), rhs);
}

const Stmt* SmackRep::storeAsBytes(unsigned region, unsigned size, const Expr* p, const Expr* e) {
  stringstream name;
  name << "$store." << intType(size);
  return Stmt::assign(Expr::id(memPath(region, 8)), Expr::fn(name.str(), Expr::id(memPath(region, 8)), p, e));
}

bool SmackRep::isFieldDisjoint(const llvm::Value* ptr, const llvm::Instruction* inst) {
  return aliasAnalysis->isFieldDisjoint(ptr, inst); 
}

bool SmackRep::isFieldDisjoint(const llvm::GlobalValue *V, unsigned offset) {
  return aliasAnalysis->isFieldDisjoint(V, offset); 
}

const Expr* SmackRep::pa(const Expr* base, unsigned long idx, unsigned long size) {
  return pa(base, pointerLit(idx), pointerLit(size));
}

const Expr* SmackRep::pa(const Expr* base, const Expr* idx, unsigned long size) {
  return pa(base, idx, pointerLit(size));
}

const Expr* SmackRep::pa(const Expr* base, const Expr* idx, const Expr* size) {
  return Expr::fn("$add.ref", base, Expr::fn("$mul.ref", idx, size));
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

const Expr* SmackRep::ptrArith(const llvm::Value* p, vector<llvm::Value*> ps, vector<llvm::Type*> ts) {

  assert(ps.size() > 0 && ps.size() == ts.size());

  const Expr* e = expr(p);

  for (unsigned i = 0; i < ps.size(); i++) {
    if (llvm::StructType* st = llvm::dyn_cast<llvm::StructType>(ts[i])) {

      assert(ps[i]->getType()->isIntegerTy()
        && ps[i]->getType()->getPrimitiveSizeInBits() == 32
        && "Illegal struct idx");

      // Get structure layout information...
      unsigned fieldNo =
        llvm::cast<llvm::ConstantInt>(ps[i])->getZExtValue();

      // Add in the offset, as calculated by the
      // structure layout info...
      e = pa(e, fieldOffset(st, fieldNo), 1);

    } else {
      llvm::Type* et =
        llvm::cast<llvm::SequentialType>(ts[i])->getElementType();
      assert(ps[i]->getType()->isIntegerTy() && "Illegal index");

      if (const llvm::ConstantInt *ci = llvm::dyn_cast<llvm::ConstantInt>(ps[i]))
        e = pa(e, (unsigned long) ci->getZExtValue(), storageSize(et));
      else
        e = pa(e, expr(ps[i]), storageSize(et));
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
    program.addDecl(Decl::constant(name,type(v->getType())));
    return Expr::id(name);

  } else if (naming.get(*v) != "")
    return Expr::id(naming.get(*v));

  else if (const Constant* constant = dyn_cast<const Constant>(v)) {

    if (const ConstantExpr* CE = dyn_cast<const ConstantExpr>(constant)) {

      if (CE->getOpcode() == Instruction::GetElementPtr) {
        vector<Value*> ps;
        vector<Type*> ts;
        gep_type_iterator typeI = gep_type_begin(CE);
        for (unsigned i = 1; i < CE->getNumOperands(); i++, ++typeI) {
          ps.push_back(CE->getOperand(i));
          ts.push_back(*typeI);
        }
        return ptrArith(CE->getOperand(0), ps, ts);

      } else if (CE->isCast())
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

string SmackRep::getString(const llvm::Value* v) {
  if (const llvm::ConstantExpr* constantExpr = llvm::dyn_cast<const llvm::ConstantExpr>(v))
    if (constantExpr->getOpcode() == llvm::Instruction::GetElementPtr)
      if (const llvm::GlobalValue* cc = llvm::dyn_cast<const llvm::GlobalValue>(constantExpr->getOperand(0)))
        if (const llvm::ConstantDataSequential* cds = llvm::dyn_cast<const llvm::ConstantDataSequential>(cc->getOperand(0)))
          return cds ->getAsCString();
  return "";
}

const Expr* SmackRep::cast(const llvm::Instruction* I) {
  return cast(I->getOpcode(), I->getOperand(0), I->getType());
}

const Expr* SmackRep::cast(const llvm::ConstantExpr* CE) {
  return cast(CE->getOpcode(), CE->getOperand(0), CE->getType());
}

string SmackRep::opName(const string& operation, initializer_list<unsigned> operands) {
  stringstream s;
  s << operation;
  for (initializer_list<unsigned>::const_iterator i = operands.begin(), e = operands.end(); i != e; ++i)
    s << "." << intType(*i);
  return s.str();
}

const Expr* SmackRep::cast(unsigned opcode, const llvm::Value* v, const llvm::Type* t) {
  using namespace llvm;
  switch (opcode) {
    case Instruction::Trunc: {
      assert(t->isIntegerTy() && "TODO: implement truncate for non-integer types.");
      return Expr::fn(opName("$trunc", {getIntSize(v), getIntSize(t)}), expr(v));
    }
         
    case Instruction::ZExt:
      return Expr::fn(opName("$zext", {getIntSize(v), getIntSize(t)}), expr(v));

    case Instruction::SExt:
      return Expr::fn(opName("$sext", {getIntSize(v), getIntSize(t)}), expr(v));

    case Instruction::FPTrunc:
    case Instruction::FPExt:
    case Instruction::BitCast:
      return expr(v);

    default:
      return Expr::fn(opName(cast2fn(opcode), {isInt(t)? getIntSize(t) : getIntSize(v)}), expr(v));
  }
}

const Expr* SmackRep::bop(const llvm::ConstantExpr* CE) {
  return bop(CE->getOpcode(), CE->getOperand(0), CE->getOperand(1), CE->getType());
}

const Expr* SmackRep::bop(const llvm::BinaryOperator* BO) {
  return bop(BO->getOpcode(), BO->getOperand(0), BO->getOperand(1), BO->getType());
}

const Expr* SmackRep::bop(unsigned opcode, const llvm::Value* lhs, const llvm::Value* rhs, const llvm::Type* t) {
  return Expr::fn( isFloat(t)
    ? bop2fn(opcode)
    : opName(bop2fn(opcode), {getIntSize(t)}), expr(lhs), expr(rhs));
}

const Expr* SmackRep::cmp(const llvm::CmpInst* I) {
  return cmp(I->getPredicate(), I->getOperand(0), I->getOperand(1));
}

const Expr* SmackRep::cmp(const llvm::ConstantExpr* CE) {
  return cmp(CE->getPredicate(), CE->getOperand(0), CE->getOperand(1));
}

const Expr* SmackRep::cmp(unsigned predicate, const llvm::Value* lhs, const llvm::Value* rhs) {
  return Expr::fn(isFloat(lhs)? pred2fn(predicate) : opName(pred2fn(predicate), {getIntSize(lhs)}), expr(lhs), expr(rhs));
}

string SmackRep::cast2fn(unsigned opcode) {
  using llvm::Instruction;
  switch (opcode) {
  case Instruction::FPToUI: return "$fp2ui";
  case Instruction::FPToSI: return "$fp2si";
  case Instruction::UIToFP: return "$ui2fp";
  case Instruction::SIToFP: return "$si2fp";
  case Instruction::PtrToInt: return "$p2i";
  case Instruction::IntToPtr: return "$i2p";
  default:
    assert(false && "Unexpected cast expression.");
  }
}

string SmackRep::bop2fn(unsigned opcode) {
  switch (opcode) {
    using llvm::Instruction;
  case Instruction::Add: return "$add";
  case Instruction::Sub: return "$sub";
  case Instruction::Mul: return "$mul";
  case Instruction::SDiv: return "$sdiv";
  case Instruction::UDiv: return "$udiv";
  case Instruction::SRem: return "$srem";
  case Instruction::URem: return "$urem";
  case Instruction::And: return "$and";
  case Instruction::Or: return "$or";
  case Instruction::Xor: return "$xor";
  case Instruction::LShr: return "$lshr";
  case Instruction::AShr: return "$ashr";
  case Instruction::Shl: return "$shl";
  case Instruction::FAdd: return "$fadd";
  case Instruction::FSub: return "$fsub";
  case Instruction::FMul: return "$fmul";
  case Instruction::FDiv: return "$fdiv";
  case Instruction::FRem: return "$frem";
  default:
    assert(false && "unexpected predicate.");
  }
}

string SmackRep::pred2fn(unsigned predicate) {
  switch (predicate) {
    using llvm::CmpInst;
  case CmpInst::ICMP_EQ: return "$eq";
  case CmpInst::ICMP_NE: return "$ne";
  case CmpInst::ICMP_SGE: return "$sge";
  case CmpInst::ICMP_UGE: return "$uge";
  case CmpInst::ICMP_SLE: return "$sle";
  case CmpInst::ICMP_ULE: return "$ule";
  case CmpInst::ICMP_SLT: return "$slt";
  case CmpInst::ICMP_ULT: return "$ult";
  case CmpInst::ICMP_SGT: return "$sgt";
  case CmpInst::ICMP_UGT: return "$ugt";
  case CmpInst::FCMP_FALSE: return "$ffalse";
  case CmpInst::FCMP_OEQ: return "$foeq";
  case CmpInst::FCMP_OGE: return "$foge";
  case CmpInst::FCMP_OGT: return "$fogt";
  case CmpInst::FCMP_OLE: return "$fole";
  case CmpInst::FCMP_OLT: return "$folt";
  case CmpInst::FCMP_ONE: return "$fone";
  case CmpInst::FCMP_ORD: return "$ford";
  case CmpInst::FCMP_TRUE: return "$ftrue";
  case CmpInst::FCMP_UEQ: return "$fueq";
  case CmpInst::FCMP_UGE: return "$fuge";
  case CmpInst::FCMP_UGT: return "$fugt";
  case CmpInst::FCMP_ULE: return "$fule";
  case CmpInst::FCMP_ULT: return "$fult";
  case CmpInst::FCMP_UNE: return "$fune";
  case CmpInst::FCMP_UNO: return "$funo";
  default:
    assert(false && "unexpected predicate.");
  }
}

string SmackRep::armwop2fn(unsigned opcode) {
  using llvm::AtomicRMWInst;
  switch (opcode) {
  case AtomicRMWInst::Add: return "$add";
  case AtomicRMWInst::Sub: return "$sub";
  case AtomicRMWInst::And: return "$and";
  case AtomicRMWInst::Nand: return "$nand";
  case AtomicRMWInst::Or: return "$or";
  case AtomicRMWInst::Xor: return "$xor";
  case AtomicRMWInst::Max: return "$max";
  case AtomicRMWInst::Min: return "$min";
  case AtomicRMWInst::UMax: return "$umax";
  case AtomicRMWInst::UMin: return "$umin";
  default:
    assert(false && "unexpected atomic operation.");
  }
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

string SmackRep::indexedName(string name, initializer_list<unsigned> idxs) {
  stringstream idxd;
  idxd << name;
  for (auto idx : idxs)
    idxd << "." << idx;
  return idxd.str();
}

vector<string> SmackRep::decl(llvm::Function* F) {
  vector<string> decls;
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

      ProcDecl* P = (ProcDecl*) Decl::procedure(program, indexedName(name,{r1,r2}), {
        make_pair("dst", type(dst)),
        make_pair("src", type(src)),
        make_pair("len", type(len)),
        make_pair("align", type(align)),
        make_pair("volatile", type(vol)),
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
      });

      program.addDecl(P);
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

      ProcDecl* P = (ProcDecl*) Decl::procedure(program, indexedName(name,{r}), {
        make_pair("dst", type(dst)),
        make_pair("val", type(val)),
        make_pair("len", type(len)),
        make_pair("align", type(align)),
        make_pair("volatile", type(vol)),
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
      });

      program.addDecl(P);
      decls.push_back(memsetProc(r));

    } else if (name == "malloc") {
      llvm::Type* T = F->getFunctionType()->getParamType(0);
      assert (T->isIntegerTy() && "Expected integer argument.");
      unsigned width = T->getIntegerBitWidth();

      ProcDecl* P = (ProcDecl*) Decl::procedure(program, name, {
        make_pair("n", type(T))
      }, {
        make_pair("r", PTR_TYPE)
      }, {
        Block::block("", {
          Stmt::call("$alloc", {integerToPointer(Expr::id("n"),width)}, {"r"})
        })
      });
      program.addDecl(P);

    } else if (name == "free_") {
      ProcDecl* P = (ProcDecl*) Decl::procedure(program, name, {
        make_pair("n", PTR_TYPE)
      }, {}, {
        Block::block("", { Stmt::call("$free", {Expr::id("n")}) })
      });
      program.addDecl(P);

    } else {
      stringstream decl;
      decl << "procedure " << name;

      if (F->isVarArg())
        for (unsigned i = 0; i < U->getNumOperands()-1; i++)
          decl << "." << type(U->getOperand(i)->getType());

      decl << "(";
      for (unsigned i = 0; i < U->getNumOperands()-1; i++) {
        if (i > 0)
          decl << ", ";
        decl << "p" << i << ":" << type(U->getOperand(i)->getType());
      }
      decl << ")";
      if (!F->getReturnType()->isVoidTy())
        decl << " returns (r: " << type(F->getReturnType()) << ")";
      decl << ";";
      decls.push_back(decl.str());

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

    parameters.push_back(make_pair(name, type(arg->getType()) ));
  }

  if (!f->getReturnType()->isVoidTy())
    returns.push_back(make_pair(Naming::RET_VAR,type(f->getReturnType())));

  return (ProcDecl*) Decl::procedure(
    program,
    f->isVarArg() ? indexedName(naming.get(*f),{}) : naming.get(*f),
    parameters,
    returns
  );
}

const Expr* SmackRep::arg(llvm::Function* f, unsigned pos, llvm::Value* v) {
  return (f && f->isVarArg() && isFloat(v)) ? Expr::fn(opName("$fp2si", {getSize(v->getType())}),expr(v)) : expr(v);
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

string functionDecl(string name, initializer_list<string> args, initializer_list<string> types, const Expr* body = 0) {
  stringstream s;
  s << "function ";
  if (body)
    s << "{:inline} ";
  s << name << "(";
  initializer_list<string>::iterator t = types.begin();
  for (initializer_list<string>::iterator a = args.begin(); a != args.end(); ++a, ++t) {
    if (a != args.begin())
      s << ", ";
    s << *a << ": " << *t;
  }
  s << ") returns (" << *t << ")";
  if (body)
    s << " { " << body << " }";
  else
    s << ";";
  return s.str();
}

string SmackRep::getPrelude() {
  stringstream s;
  s << endl;

  s << "// Basic types" << endl;
  s << "type i1 = int;" << endl;
  for (unsigned i = 8; i <= 64; i <<= 1)
    s << "type i" << i << " = int;" << endl;
  s << "type ref = " << pointerType() << ";" << endl;
  s << endl;

  s << "// Basic constants" << endl;
  s << "const $0: " << intType(32) << ";" << endl;
  s << "axiom $0 == " << integerLit(0UL,32) << ";" << endl;

  s << "const $0.ref, $1.ref, $2.ref, $3.ref, $4.ref, $5.ref, $6.ref, $7.ref: ref;" << endl;
  for (unsigned i = 0; i < 8; ++i)
    s << "axiom $" << i << ".ref == " << pointerLit((unsigned long) i) << ";" << endl;
  s << endl;

  s << "// Memory maps (" << memoryRegions.size() << " regions)" << endl;
  for (unsigned i=0; i<memoryRegions.size(); ++i) {
    unsigned n = !SmackOptions::BitPrecise || SmackOptions::NoByteAccessInference ? 1 : 4;
    for (unsigned j = 0; j < n; j++) {
      unsigned size = 8 << j;
      s << "var " << memPath(i, size) 
        << ": " << memType(i, size) 
        << ";" << endl;
    }
  }
  s << endl;

  s << "// Memory address bounds" << endl;
  s << "axiom " << GLOBALS_BOTTOM << " == " << pointerLit(globalsBottom) << ";" << endl;
  s << "axiom " << EXTERNS_BOTTOM << " == " << pointerLit(externsBottom) << ";" << endl;
  s << "axiom " << MALLOC_TOP << " == " << pointerLit((unsigned long) INT_MAX - 10485760) << ";" << endl;
  s << endl;

  s << "// Bitvector-integer conversions" << endl;
  s << "function {:builtin \"bv2int\"} $bv2int." << ptrSizeInBits
    << "(i: bv" << ptrSizeInBits << ") returns (i" << ptrSizeInBits << ");"
    << endl;
  s << "function {:builtin \"int2bv\", " << ptrSizeInBits << "} $int2bv." << ptrSizeInBits
    << "(i: i" << ptrSizeInBits << ") returns (bv" << ptrSizeInBits << ");"
    << endl;
  s << endl;

  s << "// Pointer-number conversions" << endl;
  for (unsigned i = 8; i <= 64; i <<= 1) {
    s << functionDecl(opName("$p2i", {i}), {"p"}, {"ref", intType(i)}, pointerToInteger(Expr::id("p"),i)) << endl;
    s << functionDecl(opName("$i2p", {i}), {"i"}, {intType(i), "ref"}, integerToPointer(Expr::id("i"),i)) << endl;
  }
  s << endl;

  s << "// Pointer predicates" << endl;
  const string predicates[] = {"$sge", "$sgt", "$sle", "$slt"};
  for (unsigned i = 0; i < 4; i++) {
    s << "function {:inline} " << predicates[i] << ".ref.bool(p1: ref, p2: ref)"
      << " returns (bool)"
      << " { " << predicates[i] << "." << pointerType() << ".bool(p1,p2) }"
      << endl;
  }
  s << endl;

  s << "// Pointer operations" << endl;
  const string operations[] = {"$add", "$sub", "$mul"};
  for (unsigned i = 0; i < 3; i++) {
    s << "function {:inline} " << operations[i] << ".ref(p1: ref, p2: ref)"
      << " returns (ref)"
      << " { " << operations[i] << "." << pointerType() << "(p1,p2) }"
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
    unsigned n = !SmackOptions::BitPrecise || SmackOptions::NoByteAccessInference ? 1 : 4;
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

void SmackRep::addInit(unsigned region, const llvm::Value* addr, const llvm::Constant* val) {
  if (const llvm::GlobalValue* V = dyn_cast<const GlobalValue>(addr)) { 
    if (SmackOptions::NoByteAccessInference)
      addInit(region, expr(addr), val, V, false);
    else
      addInit(region, expr(addr), val, V, isFieldDisjoint(V, 0));
  }
  else
    assert(0 && "addInit() should initialize global values?");
}

void SmackRep::addInit(unsigned region, const Expr* addr, const llvm::Constant* val, const llvm::GlobalValue* V, bool safety) {
  using namespace llvm;

  if (isInt(val)) {
    staticInits.push_back( SmackOptions::BitPrecise? (safety? Stmt::assign(mem(region, addr, getIntSize(val)), expr(val)) : storeAsBytes(region, getIntSize(val), addr, expr(val))) : Stmt::assign(mem(region,addr), expr(val)) );

  } else if (isFloat(val)) {
    staticInits.push_back( SmackOptions::BitPrecise? storeAsBytes(region, targetData->getTypeSizeInBits(val->getType()), addr, Expr::fn(opName("$fp2si", {getSize(val->getType())}),expr(val))) : Stmt::assign(mem(region,addr), Expr::fn(opName("$fp2si", {getSize(val->getType())}),expr(val))) );

  } else if (isa<PointerType>(val->getType())) {
    // TODO
    staticInits.push_back( SmackOptions::BitPrecise? storeAsBytes(region, targetData->getTypeSizeInBits(val->getType()), addr, expr(val)) : Stmt::assign(mem(region,addr), expr(val)) );

  } else if (ArrayType* at = dyn_cast<ArrayType>(val->getType())) {
    for (unsigned i = 0; i < at->getNumElements(); i++) {
      const Constant* elem = val->getAggregateElement(i);
      if (SmackOptions::NoByteAccessInference)
        addInit( region, pa(addr,i,storageSize(at->getElementType())), elem, V, false);  
      else
        addInit( region, pa(addr,i,storageSize(at->getElementType())), elem, V, isFieldDisjoint(V, i*storageSize(at->getElementType())));
    }

  } else if (StructType* st = dyn_cast<StructType>(val->getType())) {
    for (unsigned i = 0; i < st->getNumElements(); i++) {
      const Constant* elem = val->getAggregateElement(i);
      if (SmackOptions::NoByteAccessInference)
        addInit( region, pa(addr,fieldOffset(st,i),1), elem, V, false);
      else
        addInit( region, pa(addr,fieldOffset(st,i),1), elem, V, isFieldDisjoint(V, fieldOffset(st, i)));
    }

  } else if (val->getType()->isX86_FP80Ty()) {
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

bool SmackRep::hasStaticInits() {
  return staticInits.size() > 0;
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

vector<Decl*> SmackRep::globalDecl(const llvm::Value* v) {
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

        addInit(getRegion(g), g, init);
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

string SmackRep::memcpyProc(unsigned dstReg, unsigned srcReg) {
  stringstream s;
  unsigned n = !SmackOptions::BitPrecise || SmackOptions::NoByteAccessInference ? 1 : 4;

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

  return s.str();
}

string SmackRep::memsetProc(unsigned dstReg) {
  stringstream s;
  unsigned n = !SmackOptions::BitPrecise || SmackOptions::NoByteAccessInference ? 1 : 4;

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

  return s.str();
}

} // namespace smack

