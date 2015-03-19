//
// This file is distributed under the MIT License. See LICENSE for details.
//
#define DEBUG_TYPE "smack-rep"
#include "smack/SmackRep.h"
#include "smack/SmackOptions.h"

namespace smack {

const string SmackRep::BOOL_TYPE = "bool";
const string SmackRep::FLOAT_TYPE = "float";
const string SmackRep::NULL_VAL = "$NULL";

const string SmackRep::NEG = "$neg";

const string SmackRep::ALLOCA = "$alloca";
const string SmackRep::MALLOC = "$malloc";
const string SmackRep::FREE = "$free";
const string SmackRep::MEMCPY = "$memcpy";

const string SmackRep::I2B = "$i2b";
const string SmackRep::B2I = "$b2i";

// used for memory model debugging
const string SmackRep::MEM_OP = "$mop";
const string SmackRep::REC_MEM_OP = "boogie_si_record_mop";
const string SmackRep::MEM_OP_VAL = "$MOP";

const Expr* SmackRep::NUL = Expr::id(NULL_VAL);

const string SmackRep::STATIC_INIT = "$static_init";

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

string SmackRep::bits_type(unsigned width) {
  stringstream s;
  if (SmackOptions::BitPrecise)
    s << "bv" << width;
  else
    s << "int";
  return s.str();
}

string SmackRep::int_type(unsigned width) {
  stringstream s;
  s << "i" << width;
  return s.str();
}

string SmackRep::type(const llvm::Type* t) {
  if (isFloat(t))
    return FLOAT_TYPE;
  else if (isInt(t))
    return int_type(getIntSize(t));
  else
    return getPtrType();
  //assert(0 && "unsupported type");
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
    s << "[" << getPtrType() << "] ";
  s << bits_type(size);
  return s.str();
}

string SmackRep::memPath(unsigned region, unsigned size) {
  if (SmackOptions::BitPrecise)
    return (memReg(region) + "." + int_type(size));
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
  const Expr* size = Expr::fn("$mul.ref", lit(storageSize(i.getAllocatedType()), ptrSizeInBits), SmackOptions::BitPrecise ? Expr::fn("$zext.i32.ref", lit(i.getArraySize())) : lit(i.getArraySize()));

  return Stmt::call(ALLOCA,size,naming.get(i));
}

const Stmt* SmackRep::memcpy(const llvm::MemCpyInst& mci) {
  stringstream name;
  name << procName(mci) << ".r" << getRegion(mci.getOperand(0)) << ".r" << getRegion(mci.getOperand(1));
  vector<const Expr*> args;
  args.push_back(expr(mci.getOperand(0)));
  args.push_back(expr(mci.getOperand(1)));
  const llvm::Value* cpySize = mci.getOperand(2);
  args.push_back((getIntSize(cpySize) == 32)? Expr::fn("$zext.i32.ref", expr(cpySize)): expr(cpySize));
  for (unsigned i = 3; i < mci.getNumOperands() - 1; i++)
    args.push_back(expr(mci.getOperand(i)));
  return Stmt::call(name.str(),args);
}

const Stmt* SmackRep::memset(const llvm::MemSetInst& msi) {
  stringstream name;
  vector<const Expr*> args;
  name << procName(msi) << ".r" << getRegion(msi.getOperand(0));
  args.push_back(expr(msi.getOperand(0)));
  args.push_back(expr(msi.getOperand(1)));
  const llvm::Value* setSize = msi.getOperand(2);
  args.push_back((getIntSize(setSize) == 32)? Expr::fn("$zext.i32.ref", expr(setSize)): expr(setSize));
  for (unsigned i = 3; i < msi.getNumOperands() - 1; i++)
    args.push_back(expr(msi.getOperand(i)));
  return Stmt::call(name.str(),args);
}

const Stmt* SmackRep::load(const llvm::Value* addr, const llvm::Value* val) {
// The tricky part is that we could expr(li) is actually expr(val) so that it is possible to pass li to val. 
  const Expr* rhs;

  if (!SmackOptions::BitPrecise || (!SmackOptions::NoByteAccessInference && isFieldDisjoint(addr, llvm::cast<const llvm::Instruction>(val))))
    rhs = mem(addr);
  else {
    stringstream name;
    name << "$load." << int_type(getElementSize(addr));
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
  name << "$store." << int_type(size);
  return Stmt::assign(Expr::id(memPath(region, 8)), Expr::fn(name.str(), Expr::id(memPath(region, 8)), p, e));
}

bool SmackRep::isFieldDisjoint(const llvm::Value* ptr, const llvm::Instruction* inst) {
  return aliasAnalysis->isFieldDisjoint(ptr, inst); 
}

bool SmackRep::isFieldDisjoint(const llvm::GlobalValue *V, unsigned offset) {
  return aliasAnalysis->isFieldDisjoint(V, offset); 
}

const Expr* SmackRep::pa(const Expr* base, unsigned idx, unsigned size,
    unsigned i_size, unsigned t_size) {
  return pa(base, lit(idx, i_size), lit(size, t_size), i_size, t_size);
}

const Expr* SmackRep::pa(const Expr* base, const Expr* idx, unsigned size,
    unsigned i_size, unsigned t_size) {
  return pa(base, idx, lit(size, t_size), i_size, t_size);
}

const Expr* SmackRep::pa(const Expr* base, const Expr* idx, const Expr* size,
    unsigned i_size, unsigned t_size) {
  if (i_size == 32) 
    // The index of struct type is 32 bit
    return Expr::fn("$add.ref", base, Expr::fn("$zext.i32.ref", Expr::fn("$mul.i32", idx, size)));
  else if (i_size == 64)
    return Expr::fn("$add.ref", base, Expr::fn("$mul.ref", idx, Expr::fn("$zext.i32.ref", size)));
  else {
    DEBUG(errs() << "index size : " << i_size << "\n");
    assert(0 && "Unhandled index type");
  }
}

const Expr* SmackRep::i2b(const llvm::Value* v) {
  return Expr::fn(I2B, expr(v));
}

const Expr* SmackRep::b2i(const llvm::Value* v) {
  return Expr::fn(B2I, expr(v));
}

const Expr* SmackRep::lit(const llvm::Value* v) {
  using namespace llvm;

  if (const ConstantInt* ci = llvm::dyn_cast<const ConstantInt>(v)) {
    unsigned w = ci->getBitWidth();
    if (w>1 && ci->isNegative()) {
      return Expr::fn(opName("$sub", {w}), lit((long)0, w), lit(ci->getValue().abs().toString(10,false),w));
    } else {
      return lit(ci->getValue().toString(10,false),w);
    }
  }

  else if (const ConstantFP* CFP = dyn_cast<const ConstantFP>(v)) {
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
    return Expr::id("$NULL");

  else
    return expr(v);
  // assert( false && "value type not supported" );
}

const Expr* SmackRep::lit(bool val) {
  return Expr::lit(val);
}

const Expr* SmackRep::lit(string val, unsigned width) {
  return SmackOptions::BitPrecise && width > 0 ? Expr::lit(val,width) : Expr::lit(val);
}

const Expr* SmackRep::lit(unsigned val, unsigned width) {
  return SmackOptions::BitPrecise && width > 0 ? Expr::lit(val,width) : Expr::lit(val);
}

const Expr* SmackRep::lit(long val, unsigned width) {
  return SmackOptions::BitPrecise && width > 0 ? Expr::lit((unsigned)val,width) : Expr::lit(val);
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
      e = pa(e, fieldOffset(st, fieldNo), 1, 32, 32);

    } else {
      llvm::Type* et =
        llvm::cast<llvm::SequentialType>(ts[i])->getElementType();
      e = pa(e, lit(ps[i]), storageSize(et), getIntSize(ps[i]), 32);
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
      return lit((unsigned)0, ptrSizeInBits);

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
    s << "." << int_type(*i);
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

string SmackRep::indexedName(string name, vector<string> idxs) {
  stringstream idxd;
  idxd << name;
  for (vector<string>::iterator i = idxs.begin(); i != idxs.end(); ++i)
    idxd << "." << *i;
  return idxd.str();
}

string SmackRep::indexedName(string name, int idx) {
  stringstream idxd;
  idxd << name << "#" << idx;
  return idxd.str();
}

vector<string> SmackRep::decl(llvm::Function* F) {
  vector<string> decls;

  for (llvm::Value::user_iterator U = F->user_begin(); U != F->user_end(); ++U)
    if (MemCpyInst* MCI = dyn_cast<MemCpyInst>(*U))
      decls.push_back(memcpyProc(F,getRegion(MCI->getOperand(0)),getRegion(MCI->getOperand(1))));

    else if (MemSetInst* MSI = dyn_cast<MemSetInst>(*U))
      decls.push_back(memsetProc(F,getRegion(MSI->getOperand(0))));

    else {
      stringstream decl;
      decl << "procedure " << naming.get(*F);

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
  vector<string> idxs;
  vector< pair<string,string> > parameters, returns;

  unsigned i = 0;
  for (llvm::Function::arg_iterator
       arg = f->arg_begin(), e = f->arg_end(); arg != e; ++arg, ++i) {
    string name;
    if (arg->hasName()) {
      name = naming.get(*arg);
    } else {
      name = indexedName("p",i);
      arg->setName(name);
    }

    parameters.push_back(make_pair(name, type(arg->getType()) ));
  }

  if (!f->getReturnType()->isVoidTy())
    returns.push_back(make_pair(Naming::RET_VAR,type(f->getReturnType())));

  return (ProcDecl*) Decl::procedure(
    program,
    f->isVarArg() ? indexedName(naming.get(*f),idxs) : naming.get(*f),
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

  if (name == "malloc") {
    assert(args.size() == 1);
    return Stmt::call(MALLOC, args[0], rets[0]);

  } else if (name == "free_") {
    assert(args.size() == 1);
    return Stmt::call(FREE, args[0]);

  } else {
    return Stmt::call(procName(ci, f), args, rets);
  }
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
  s << endl;
  s << "// Memory region declarations";
  s << ": " << memoryRegions.size() << endl;
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
  s << "// Type declarations" << endl;
  for (unsigned i = 1; i <= 64; i <<= 1) {
    s << "type " << int_type(i) << " = " << bits_type(i) << ";" << endl; 
  }

  s << "type ref = " << bits_type(ptrSizeInBits) << ";" << endl; 
  s << "type size = " << bits_type(ptrSizeInBits) << ";" << endl; 
  for (int i = 1; i < 8; ++i) {
    s << "axiom $REF_CONST_" << i << " == ";
    lit((unsigned)i,ptrSizeInBits)->print(s);
    s << ";" << endl;
  }
  s << "function {:inline} $zext.i32.ref(p: i32) returns (ref) {" << ((ptrSizeInBits == 32)? "p}" : "$zext.i32.i64(p)}") << endl;

  for (unsigned i = 8; i <= 64; i <<= 1) {
    if (i < ptrSizeInBits) {
      s << "function {:inline}" << opName("$p2i", {i}) << "(p: ref) returns (" << int_type(i) << ") {" << opName("$trunc", {ptrSizeInBits, i}) << "(p)}" << endl;
      s << "function {:inline}" << opName("$i2p", {i}) << "(p: " << int_type(i) << ") returns (ref) {" << opName("$zext", {i, ptrSizeInBits}) << "(p)}" << endl;
    } else if (i > ptrSizeInBits) {
      s << "function {:inline}" << opName("$p2i", {i}) << "(p: ref) returns (" << int_type(i) << ") {" << opName("$zext", {ptrSizeInBits, i}) << "(p)}" << endl;
      s << "function {:inline}" << opName("$i2p", {i}) << "(p: " << int_type(i) << ") returns (ref) {" << opName("$trunc", {i, ptrSizeInBits}) << "(p)}" << endl;
    } else {
      s << "function {:inline}" << opName("$p2i", {i}) << "(p: ref) returns (" << int_type(i) << ") {p}" << endl;
      s << "function {:inline}" << opName("$i2p", {i}) << "(p: " << int_type(i) << ") returns (ref) {p}" << endl;
    }
  }

  s << "axiom $NULL == ";
  lit((long)0,ptrSizeInBits)->print(s); 
  s << ";" << endl; 
  s << endl;

  s << "axiom $GLOBALS_BOTTOM == ";
  lit(globalsBottom, ptrSizeInBits)->print(s);
  s << ";" << endl;

  s << "axiom $EXTERNS_BOTTOM == ";
  lit(externsBottom, ptrSizeInBits)->print(s);
  s << ";" << endl;

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
        addInit( region, pa(addr,i,storageSize(at->getElementType()), 32, 32), elem, V, false);  
      else
        addInit( region, pa(addr,i,storageSize(at->getElementType()), 32, 32), elem, V, isFieldDisjoint(V, i*storageSize(at->getElementType())));
    }

  } else if (StructType* st = dyn_cast<StructType>(val->getType())) {
    for (unsigned i = 0; i < st->getNumElements(); i++) {
      const Constant* elem = val->getAggregateElement(i);
      if (SmackOptions::NoByteAccessInference)
        addInit( region, pa(addr,fieldOffset(st,i),1, 32, 32), elem, V, false);
      else
        addInit( region, pa(addr,fieldOffset(st,i),1, 32, 32), elem, V, isFieldDisjoint(V, fieldOffset(st, i)));
    }

  } else if (val->getType()->isX86_FP80Ty()) {
    staticInits.push_back(Stmt::code("// ignored X86 FP80 initializer"));

  } else {
    assert (false && "Unexpected static initializer.");
  }
}

bool SmackRep::hasStaticInits() {
  return staticInits.size() > 0;
}

Decl* SmackRep::getStaticInit() {
  ProcDecl* proc = (ProcDecl*) Decl::procedure(program, STATIC_INIT);
  Block* b = new Block();

  b->addStmt( Stmt::assign(Expr::id("$CurrAddr"), lit((long)1024,ptrSizeInBits)) );
  for (unsigned i=0; i<staticInits.size(); i++)
    b->addStmt(staticInits[i]);
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

  decls.push_back(Decl::constant(name, getPtrType(), ax, false));

  if (!size)
    size = targetData->getPrefTypeAlignment(v->getType());

  decls.push_back(Decl::axiom(Expr::eq(Expr::id(name),lit(
    external ? externsBottom -= size : globalsBottom -= size,
    ptrSizeInBits))));

  return decls;
}

const Expr* SmackRep::declareIsExternal(const Expr* e) {
  return Expr::fn("$isExternal",e);
}

string SmackRep::getPtrType() {
  return "ref";
}

string SmackRep::memcpyProc(llvm::Function* F, int dstReg, int srcReg) {
  stringstream s;
  unsigned n = !SmackOptions::BitPrecise || SmackOptions::NoByteAccessInference ? 1 : 4;

  s << "procedure " << naming.get(*F) << ".r" << dstReg << ".r" << srcReg;
  s << "(dest: ref, src: ref, len: size, align: i32, isvolatile: i1)";
  s << (SmackOptions::MemoryModelImpls ? "" : ";") << endl;

  for (unsigned i = 0; i < n; ++i)
    s << "modifies " << memPath(dstReg, 8 << i) << ";" << endl;

  if (SmackOptions::MemoryModelImpls) {
    s << "{" << endl;
    for (unsigned i = 0; i < n; ++i) {
      unsigned size = 8 << i;
      s << "  var $oldSrc" << ".i" << size << " : [" << getPtrType() << "] " << int_type(size) << ";" << endl;
      s << "  var $oldDst" << ".i" << size << " : [" << getPtrType() << "] " << int_type(size) << ";" << endl;
    }
    for (unsigned i = 0; i < n; ++i) {
      unsigned size = 8 << i;
      s << "  $oldSrc" << ".i" << size << " := " << memPath(srcReg, size) << ";" << endl;
      s << "  $oldDst" << ".i" << size << " := " << memPath(dstReg, size) << ";" << endl;
      s << "  havoc " << memPath(dstReg, size) << ";" << endl;
      s << "  assume (forall x:ref :: $i2b($sle.ref(dest, x)) && $i2b($slt.ref(x, $add.ref(dest, len))) ==> "
        << memPath(dstReg, size) << "[x] == $oldSrc" << ".i" << size << "[$add.ref($sub.ref(src, dest), x)]);" << endl;
      s << "  assume (forall x:ref :: !($i2b($sle.ref(dest, x)) && $i2b($slt.ref(x, $add.ref(dest, len)))) ==> "
        << memPath(dstReg, size) << "[x] == $oldDst" << ".i" << size << "[x]);" << endl;
    }
    s << "}" << endl;
  } else {
    for (unsigned i = 0; i < n; ++i) {
      unsigned size = 8 << i;
      s << "ensures (forall x:ref :: $i2b($sle.ref(dest, x)) && $i2b($slt.ref(x, $add.ref(dest, len))) ==> "
        << memPath(dstReg, size) << "[x] == old(" << memPath(srcReg, size) << ")[$add.ref($sub.ref(src, dest), x)]);" 
        << endl;
      s << "ensures (forall x:ref :: !($i2b($sle.ref(dest, x)) && $i2b($slt.ref(x, $add.ref(dest, len)))) ==> "
        << memPath(dstReg, size) << "[x] == old(" << memPath(dstReg, size) << ")[x]);" << endl;
    }
  }

  return s.str();
}

string SmackRep::memsetProc(llvm::Function* F, int dstReg) {
  stringstream s;
  unsigned n = !SmackOptions::BitPrecise || SmackOptions::NoByteAccessInference ? 1 : 4;

  s << "procedure " << naming.get(*F) << ".r" << dstReg;
  s << "(dest: ref, val: i8, len: size, align: i32, isvolatile: i1)";
  s << (SmackOptions::MemoryModelImpls ? "" : ";") << endl;

  for (unsigned i = 0; i < n; ++i)
    s << "modifies " << memPath(dstReg, 8 << i) << ";" << endl;

  if (SmackOptions::MemoryModelImpls) {
    s << "{" << endl;
    for (unsigned i = 0; i < n; ++i) {
      unsigned size = 8 << i;
      s << "  var $oldDst" << ".i" << size << " : [" << getPtrType() << "] " << int_type(size) << ";" << endl;
    }

    string val = "val";
    for (unsigned i = 0; i < n; ++i) {
      unsigned size = 8 << i;
      s << "  $oldDst" << ".i" << size << " := " << memPath(dstReg, size) << ";" << endl;
      s << "  havoc " << memPath(dstReg, size) << ";" << endl;
      s << "  assume (forall x:ref :: $i2b($sle.ref(dest, x)) && $i2b($slt.ref(x, $add.ref(dest, len))) ==> "
        << memPath(dstReg, size) << "[x] == "
        << val
        << ");" << endl;
      s << "  assume (forall x:ref :: !($i2b($sle.ref(dest, x)) && $i2b($slt.ref(x, $add.ref(dest, len)))) ==> "
        << memPath(dstReg, size) << "[x] == $oldDst" << ".i" << size << "[x]);" << endl;
      val = val + "++" + val;
    }
    s << "}" << endl;
  } else {
    string val = "val";
    for (unsigned i = 0; i < n; ++i) {
      unsigned size = 8 << i;
      s << "ensures (forall x:ref :: $i2b($sle.ref(dest, x)) && $i2b($slt.ref(x, $add.ref(dest, len))) ==> "
        << memPath(dstReg, size) << "[x] == "
        << val
        << ");" << endl;
      s << "ensures (forall x:ref :: !($i2b($sle.ref(dest, x)) && $i2b($slt.ref(x, $add.ref(dest, len)))) ==> "
        << memPath(dstReg, size) << "[x] == old(" << memPath(dstReg, size) << ")[x]);" << endl;
      val = val + "++" + val;
    }
  }

  return s.str();
}

} // namespace smack

