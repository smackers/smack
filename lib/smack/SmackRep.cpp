//
// This file is distributed under the MIT License. See LICENSE for details.
//
#define DEBUG_TYPE "smack-rep"
#include "smack/SmackRep.h"
#include "smack/SmackOptions.h"

#include <iostream>

namespace smack {

const string SmackRep::BOOL_TYPE = "bool";
const string SmackRep::FLOAT_TYPE = "float";
const string SmackRep::NULL_VAL = "$NULL";

const string SmackRep::ALLOCA = "$alloca";
const string SmackRep::MALLOC = "$malloc";
const string SmackRep::FREE = "$free";
const string SmackRep::MEMCPY = "$memcpy";

const string SmackRep::B2P = "$b2p";
const string SmackRep::I2B = "$i2b";
const string SmackRep::B2I = "$b2i";

// used for memory model debugging
const string SmackRep::MEM_OP = "$mop";
const string SmackRep::REC_MEM_OP = "boogie_si_record_mop";
const string SmackRep::MEM_OP_VAL = "$MOP";

const Expr* SmackRep::NUL = Expr::id(NULL_VAL);

const string SmackRep::STATIC_INIT = "$static_init";

const int SmackRep::width = 0;

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

bool SmackRep::isBool(const llvm::Type* t) {
  return t->isIntegerTy(1);
}

bool SmackRep::isBool(const llvm::Value* v) {
  return isBool(v->getType());
}

bool SmackRep::isFloat(const llvm::Type* t) {
  return t->isFloatingPointTy();
}

bool SmackRep::isFloat(const llvm::Value* v) {
  return isFloat(v->getType());
}

string SmackRep::type(const llvm::Type* t) {
  if (isBool(t))
    return BOOL_TYPE;
  else if (isFloat(t))
    return FLOAT_TYPE;
  else
    return getPtrType();
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

string SmackRep::memType(unsigned r) {
  if (memoryRegions[r].isSingletonGlobal)
    return getPtrType();
  else {
    return "[int] int";
    stringstream s;
    s << "[" << getPtrType() << "] " + getPtrType();
    return s.str();
  }
}

const Expr* SmackRep::mem(const llvm::Value* v) {
  unsigned r = getRegion(v);
  if (memoryRegions[r].isSingletonGlobal)
    return Expr::id(memReg(r));
  else
    return Expr::sel(Expr::id(memReg(r)),expr(v));
}

const Expr* SmackRep::mem(unsigned region, const Expr* addr) {
  if (memoryRegions[region].isSingletonGlobal)
    return Expr::id(memReg(region));
  else
    return Expr::sel(Expr::id(memReg(region)),addr);
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
    Expr::fn("$mul",lit(storageSize(i.getAllocatedType())),lit(i.getArraySize()));
                       
  return Stmt::call(ALLOCA,size,naming.get(i));
}

const Stmt* SmackRep::memcpy(const llvm::MemCpyInst& mci) {
  int dstRegion = getRegion(mci.getOperand(0));
  int srcRegion = getRegion(mci.getOperand(1));

  program.addDecl(memcpyProc(dstRegion,srcRegion));

  stringstream name;
  name << "$memcpy." << dstRegion << "." << srcRegion;
  vector<const Expr*> args;
  for (unsigned i = 0; i < mci.getNumOperands() - 1; i++)
    args.push_back(expr(mci.getOperand(i)));
  return Stmt::call(name.str(),args);
}

const Stmt* SmackRep::memset(const llvm::MemSetInst& msi) {
  int region = getRegion(msi.getOperand(0));

  program.addDecl(memsetProc(region));

  stringstream name;
  vector<const Expr*> args;
  name << "$memset." << region;
  for (unsigned i = 0; i < msi.getNumOperands() - 1; i++)
    args.push_back(expr(msi.getOperand(i)));
  return Stmt::call(name.str(),args);
}

const Expr* SmackRep::pa(const Expr* base, int index, int size) {
  return pa(base, Expr::lit(index), Expr::lit(size));
}
const Expr* SmackRep::pa(const Expr* base, const Expr* index, int size) {
  return pa(base, index, Expr::lit(size));
}
const Expr* SmackRep::pa(const Expr* base, const Expr* index, const Expr* size) {
  return Expr::fn("$pa", base, index, size);
}
const Expr* SmackRep::b2p(const llvm::Value* v) {
  return Expr::fn(B2P, expr(v));
}
const Expr* SmackRep::i2b(const llvm::Value* v) {
  return Expr::fn(I2B, expr(v));
}
const Expr* SmackRep::b2i(const llvm::Value* v) {
  return Expr::fn(B2I, expr(v));
}

const Expr* SmackRep::lit(const llvm::Value* v) {
  using namespace llvm;

  if (const llvm::ConstantInt* ci = llvm::dyn_cast<const llvm::ConstantInt>(v)) {
    if (ci->getBitWidth() == 1)
      return Expr::lit(!ci->isZero());

    uint64_t val = ci->getLimitedValue();
    if (width > 0 && ci->isNegative())
      return Expr::fn("$sub", Expr::lit(0, width), Expr::lit(-val, width));
    else
      return Expr::lit(val, width);

  } else if (const ConstantFP* CFP = dyn_cast<const ConstantFP>(v)) {
    const APFloat APF = CFP->getValueAPF();
    string str;
    raw_string_ostream ss(str);
    ss << *CFP;
    istringstream iss(str);
    string float_type;
    int integerPart, fractionalPart, exponentPart;
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

  } else if (llvm::isa<llvm::ConstantPointerNull>(v))
    return Expr::lit(0, width);

  else
    return expr(v);
  // assert( false && "value type not supported" );
}

const Expr* SmackRep::lit(unsigned v) {
  // TODO why doesn't this one do the thing with negative as well?
  return Expr::lit(v, width);
}

const Expr* SmackRep::ptrArith(
  const llvm::Value* p, vector<llvm::Value*> ps, vector<llvm::Type*> ts) {

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
      e = pa(e, lit(ps[i]), storageSize(et));
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
      if (ci->getBitWidth() == 1)
        return Expr::lit(!ci->isZero());

      else return lit(ci);
      
    } else if (const ConstantFP* cf = dyn_cast<const ConstantFP>(constant)) {
      return lit(cf);

    } else if (constant->isNullValue())
      return lit((unsigned)0);

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

const Expr* SmackRep::cast(unsigned opcode, const llvm::Value* v, const llvm::Type* t) {
  using namespace llvm;
  switch (opcode) {
  case Instruction::Trunc:
    assert(t->isIntegerTy() && "TODO: implement truncate for non-integer types.");
    return isBool(t)
      ? Expr::fn("$i2b",expr(v))
      : Expr::fn("$trunc",expr(v),lit(t->getPrimitiveSizeInBits()));

  case Instruction::ZExt:
  case Instruction::SExt:
    return isBool(v->getType()) ? b2p(v) : expr(v);

  case Instruction::FPTrunc:
  case Instruction::FPExt:
  case Instruction::BitCast:
    return expr(v);

  default:
    return Expr::fn(cast2fn(opcode), expr(v));
  }
}

const Expr* SmackRep::bop(const llvm::ConstantExpr* CE) {
  return bop(CE->getOpcode(), CE->getOperand(0), CE->getOperand(1), CE->getType());
}

const Expr* SmackRep::bop(const llvm::BinaryOperator* BO) {
  return bop(BO->getOpcode(), BO->getOperand(0), BO->getOperand(1), BO->getType());
}

const Expr* SmackRep::bop(unsigned opcode, const llvm::Value* lhs, const llvm::Value* rhs, const llvm::Type* t) {
  const Expr* e = Expr::fn(bop2fn(opcode),
                           (isBool(lhs) ? b2i(lhs) : expr(lhs)),
                           (isBool(rhs) ? b2i(rhs) : expr(rhs)));

  return isBool(t) ? Expr::fn("$i2b",e) : e;
}

const Expr* SmackRep::cmp(const llvm::CmpInst* I) {
  return cmp(I->getPredicate(), I->getOperand(0), I->getOperand(1));
}

const Expr* SmackRep::cmp(const llvm::ConstantExpr* CE) {
  return cmp(CE->getPredicate(), CE->getOperand(0), CE->getOperand(1));
}

const Expr* SmackRep::cmp(unsigned predicate, const llvm::Value* lhs, const llvm::Value* rhs) {
  using namespace llvm;
  switch (predicate) {
    using llvm::CmpInst;
  case CmpInst::ICMP_EQ:
    return Expr::eq(expr(lhs), expr(rhs));
  case CmpInst::ICMP_NE:
    return Expr::neq(expr(lhs), expr(rhs));
  default:
    return Expr::fn(pred2fn(predicate), expr(lhs), expr(rhs));
  }
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

string indexedName(string name, int idx) {
  stringstream idxd;
  idxd << name << "#" << idx;
  return idxd.str();
}

ProcDecl* SmackRep::proc(llvm::Function* f, int nargs) {
  vector< pair<string,string> > args, rets;

  int i = 0;
  for (llvm::Function::arg_iterator
       arg = f->arg_begin(), e = f->arg_end(); arg != e; ++arg, ++i) {
    string name;
    if (arg->hasName()) {
      name = naming.get(*arg);
    } else {
      name = indexedName("p",i);
      arg->setName(name);
    }
    
    args.push_back(make_pair(name, type(arg->getType()) ));
  }
  
  for (; i < nargs; i++)
    args.push_back(make_pair(indexedName("p",i), getPtrType()));

  if (!f->getReturnType()->isVoidTy())
    rets.push_back(make_pair(Naming::RET_VAR,type(f->getReturnType())));

  return (ProcDecl*) Decl::procedure(
    program,
    f->isVarArg() ? indexedName(naming.get(*f),nargs) : naming.get(*f), 
    args, 
    rets
  );
}

const Expr* SmackRep::arg(llvm::Function* f, unsigned pos, llvm::Value* v) {
  return (f && f->isVarArg() && isFloat(v)) ? Expr::fn("$fp2si",expr(v)) : expr(v);
}

const Stmt* SmackRep::call(llvm::Function* f, llvm::User& ci) {
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

  } else if (f->isVarArg() || (f->isDeclaration() && !Naming::isSmackName(name))) {
    
    Decl* p = proc(f,args.size());
    program.addDecl(p);
    return Stmt::call(p->getName(), args, rets);
    
  } else {
    return Stmt::call(name, args, rets);
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
  for (unsigned i=0; i<memoryRegions.size(); ++i)
    s << "var " << memReg(i) << ": " << memType(i) << ";" << endl;
  s << endl;
  s << "axiom $GLOBALS_BOTTOM == " << globalsBottom << ";" << endl;

  return s.str();
}

void SmackRep::addBplGlobal(string name) {
  bplGlobals.push_back(name);
}

vector<string> SmackRep::getModifies() {
  vector<string> mods;
  for (vector<string>::iterator i = bplGlobals.begin(); i != bplGlobals.end(); ++i)
    mods.push_back(*i);
  for (unsigned i=0; i<memoryRegions.size(); ++i)
    mods.push_back(memReg(i));
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
  addInit(region, expr(addr), val);
}

void SmackRep::addInit(unsigned region, const Expr* addr, const llvm::Constant* val) {
  using namespace llvm;

  if (isInt(val)) {
    staticInits.push_back( Stmt::assign(mem(region,addr), expr(val)) );

  } else if (isFloat(val)) {
    staticInits.push_back( Stmt::assign(mem(region,addr), Expr::fn("$fp2si",expr(val))) );

  } else if (isa<PointerType>(val->getType())) {
    staticInits.push_back( Stmt::assign(mem(region,addr), expr(val)) );

  } else if (ArrayType* at = dyn_cast<ArrayType>(val->getType())) {

    for (unsigned i = 0; i < at->getNumElements(); i++) {
      const Constant* elem = val->getAggregateElement(i);
      addInit( region, pa(addr,i,storageSize(at->getElementType())), elem );
    }

  } else if (StructType* st = dyn_cast<StructType>(val->getType())) {
    for (unsigned i = 0; i < st->getNumElements(); i++) {
      const Constant* elem = val->getAggregateElement(i);
      addInit( region, pa(addr,fieldOffset(st,i),1), elem );
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
  for (unsigned i=0; i<staticInits.size(); i++)
    b->addStmt(staticInits[i]);
  b->addStmt(Stmt::return_());
  proc->addBlock(b);
  return proc;
}
Regex STRING_CONSTANT("^\\.str[0-9]*$");

vector<Decl*> SmackRep::globalDecl(const llvm::Value* v) {
  using namespace llvm;
  vector<Decl*> decls;
  vector<const Attr*> ax;
  string name = naming.get(*v);

  if (const GlobalVariable* g = dyn_cast<const GlobalVariable>(v)) {
    if (g->hasInitializer()) {
      const Constant* init = g->getInitializer();
      unsigned numElems = numElements(init);
      unsigned size;

      // NOTE: all global variables have pointer type in LLVM
      if (g->getType()->isPointerTy()) {
        PointerType *t = (PointerType*) g->getType();

        // in case we can determine the size of the element type ...
        if (t->getElementType()->isSized())
          size = storageSize(t->getElementType());

        // otherwise (e.g. for function declarations), use a default size
        else
          size = 1024;

      } else
        size = storageSize(g->getType());

      globalsBottom -= size;

      if (!g->hasName() || !STRING_CONSTANT.match(g->getName().str())) {
        if (numElems > 1)
          ax.push_back(Attr::attr("count",numElems));

        decls.push_back(Decl::axiom(Expr::eq(Expr::id(name),Expr::lit(globalsBottom))));
        addInit(getRegion(g), g, init);

        // Expr::fn("$slt",
        //     Expr::fn(SmackRep::ADD, Expr::id(name), Expr::lit(1024)),
        //     Expr::lit(globalsBottom)) ));
      }

    } else {
      decls.push_back(Decl::axiom(declareIsExternal(Expr::id(name))));
    }
  }
  decls.push_back(Decl::constant(name, getPtrType(), ax, true));
  return decls;
}

const Expr* SmackRep::declareIsExternal(const Expr* e) {
  return Expr::fn("$isExternal",e);
}

string SmackRep::getPtrType() {
  return "int";
}

string SmackRep::memcpyProc(int dstReg, int srcReg) {
  stringstream s;

  if (SmackOptions::MemoryModelImpls) {
    s << "procedure $memcpy." << dstReg << "." << srcReg;
    s << "(dest: int, src: int, len: int, align: int, isvolatile: bool)" << endl;
    s << "modifies " << memReg(dstReg) << ";" << endl;
    s << "{" << endl;
    s << "  var $oldSrc: [" << getPtrType() << "] " << getPtrType() << ";" << endl;
    s << "  var $oldDst: [" << getPtrType() << "] " << getPtrType() << ";" << endl;
    s << "  $oldSrc := " << memReg(srcReg) << ";" << endl;
    s << "  $oldDst := " << memReg(dstReg) << ";" << endl;
    s << "  havoc " << memReg(dstReg) << ";" << endl;
    s << "  assume (forall x:int :: dest <= x && x < dest + len ==> "
      << memReg(dstReg) << "[x] == $oldSrc[src - dest + x]);" << endl;
    s << "  assume (forall x:int :: !(dest <= x && x < dest + len) ==> "
      << memReg(dstReg) << "[x] == $oldDst[x]);" << endl;
    s << "}" << endl;
  } else {
    s << "procedure $memcpy." << dstReg << "." << srcReg;
    s << "(dest: int, src: int, len: int, align: int, isvolatile: bool);" << endl;
    s << "modifies " << memReg(dstReg) << ";" << endl;
    s << "ensures (forall x:int :: dest <= x && x < dest + len ==> "
      << memReg(dstReg) << "[x] == old(" << memReg(srcReg) << ")[src - dest + x]);" 
      << endl;
    s << "ensures (forall x:int :: !(dest <= x && x < dest + len) ==> "
      << memReg(dstReg) << "[x] == old(" << memReg(dstReg) << ")[x]);" << endl;
  }

  return s.str();
}

string SmackRep::memsetProc(int dstReg) {
  stringstream s;

  if (SmackOptions::MemoryModelImpls) {
    s << "procedure $memset." << dstReg;
    s << "(dest: int, val: int, len: int, align: int, isvolatile: bool)" << endl;
    s << "modifies " << memReg(dstReg) << ";" << endl;
    s << "{" << endl;
    s << "  var $oldDst: [" << getPtrType() << "] " << getPtrType() << ";" << endl;
    s << "  $oldDst := " << memReg(dstReg) << ";" << endl;
    s << "  havoc " << memReg(dstReg) << ";" << endl;
    s << "  assume (forall x:int :: dest <= x && x < dest + len ==> "
      << memReg(dstReg) << "[x] == val);" << endl;
    s << "  assume (forall x:int :: !(dest <= x && x < dest + len) ==> "
      << memReg(dstReg) << "[x] == $oldDst[x]);" << endl;
    s << "}" << endl;
  } else {
    s << "procedure $memset." << dstReg;
    s << "(dest: int, val: int, len: int, align: int, isvolatile: bool);" << endl;
    s << "modifies " << memReg(dstReg) << ";" << endl;
    s << "ensures (forall x:int :: dest <= x && x < dest + len ==> "
      << memReg(dstReg) << "[x] == val);"
      << endl;
    s << "ensures (forall x:int :: !(dest <= x && x < dest + len) ==> "
      << memReg(dstReg) << "[x] == old(" << memReg(dstReg) << ")[x]);" << endl;
  }

  return s.str();
}

} // namespace smack

