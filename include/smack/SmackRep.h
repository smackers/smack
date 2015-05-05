//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACKREP_H
#define SMACKREP_H

#include "smack/Naming.h"
#include "smack/BoogieAst.h"
#include "smack/SmackOptions.h"
#include "smack/DSAAliasAnalysis.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/Support/GraphWriter.h"
#include "llvm/Support/Regex.h"
#include <sstream>
#include <set>

namespace smack {

using llvm::Regex;
using llvm::SmallVector;
using llvm::StringRef;
using namespace std;
  
class SmackRep {
public:
  static const string NEG;

  static const string BOOL_TYPE;
  static const string FLOAT_TYPE;
  static const string PTR_TYPE;

  static const string NULL_VAL;
  static const string GLOBALS_BOTTOM;
  static const string EXTERNS_BOTTOM;
  static const string MALLOC_TOP;

  static const string ALLOCA;
  static const string MALLOC;
  static const string FREE;
  static const string MEMCPY;

  static const string MEM_OP;
  static const string REC_MEM_OP;
  static const string MEM_OP_VAL;

  static const string STATIC_INIT;
  static const string INIT_FUNCS;

  static const map<unsigned,string> INSTRUCTION_TABLE;
  static const map<unsigned,string> CMPINST_TABLE;
  static const map<unsigned,string> ATOMICRMWINST_TABLE;

protected:
  DSAAliasAnalysis* aliasAnalysis;
  Naming& naming;
  Program& program;
  vector<string> bplGlobals;

  struct Region {
    const llvm::Value* representative;
    bool isAllocated;
    bool isSingletonGlobal;
    Region(const llvm::Value* r, bool a, bool s) :
      representative(r), isAllocated(a), isSingletonGlobal(s) {}
  };

  vector<Region> memoryRegions;
  const llvm::DataLayout* targetData;
  unsigned ptrSizeInBits;

  long globalsBottom;
  long externsBottom;
  vector<const Stmt*> staticInits;
  vector<const Stmt*> initFuncs;
  
  unsigned uniqueFpNum;

public:
  SmackRep(DSAAliasAnalysis* aa, Naming& N, Program& P)
    : aliasAnalysis(aa), naming(N), program(P),
      targetData(aa->getDataLayout()), globalsBottom(0), externsBottom(-32768) {
    uniqueFpNum = 0;
    ptrSizeInBits = targetData->getPointerSizeInBits();
  }
  DSAAliasAnalysis* getAliasAnalysis() { return aliasAnalysis; }
  Program& getProgram() { return program; }

private:
  void addInit(const llvm::GlobalValue* G, const llvm::Constant* C);
  void addInit(const llvm::GlobalValue* G, const Expr* addr, const llvm::Constant* C, bool bytewise);

  unsigned storageSize(llvm::Type* T);
  unsigned offset(llvm::ArrayType* T, unsigned idx);
  unsigned offset(llvm::StructType* T, unsigned idx);

  const Expr* pa(const Expr* base, unsigned long index, unsigned long size);
  const Expr* pa(const Expr* base, const Expr* index, unsigned long size);
  const Expr* pa(const Expr* base, unsigned long offset);
  const Expr* pa(const Expr* base, const Expr* index, const Expr* size);
  const Expr* pa(const Expr* base, const Expr* offset);
  
  const Expr* bitConversion(const Expr* e, bool src, bool dst);
  const Expr* pointerToInteger(const Expr* e, unsigned width);
  const Expr* integerToPointer(const Expr* e, unsigned width);

  string opName(const string& operation, initializer_list<const llvm::Type*> types);
  string opName(const string& operation, initializer_list<unsigned> types);

  const Expr* mem(unsigned region, const Expr* addr, unsigned size);
  const Stmt* store(unsigned region, unsigned size, const Expr* addr, const llvm::Value* val, bool bytewise = false);

  const Expr* cast(unsigned opcode, const llvm::Value* v, const llvm::Type* t);
  const Expr* bop(unsigned opcode, const llvm::Value* lhs, const llvm::Value* rhs, const llvm::Type* t);
  const Expr* cmp(unsigned predicate, const llvm::Value* lhs, const llvm::Value* rhs);

  string procName(const llvm::User& U);
  string procName(const llvm::User& U, llvm::Function* F);

  bool uniformMemoryAccesses();
  bool bytewiseAccess(const llvm::Value* V, const llvm::Function* F);
  bool bytewiseAccess(const llvm::GlobalValue* V, unsigned offset);

public:
  unsigned getElementSize(const llvm::Value* v);
  unsigned getIntSize(const llvm::Value* v);
  unsigned getIntSize(const llvm::Type* t);
  unsigned getSize(llvm::Type* t);

  string getString(const llvm::Value* v);

  unsigned getRegion(const llvm::Value* v);
  string memReg(unsigned i);
  string memType(unsigned region, unsigned size);
  string memPath(unsigned region, unsigned size);
  bool isExternal(const llvm::Value* v);
  void collectRegions(llvm::Module &M);

  string pointerType();
  string intType(unsigned width);

  const Expr* pointerLit(unsigned v) { return pointerLit((unsigned long) v); }
  const Expr* pointerLit(unsigned long v);
  const Expr* pointerLit(long v);
  const Expr* integerLit(unsigned v, unsigned width) { return integerLit((unsigned long) v, width); }
  const Expr* integerLit(unsigned long v, unsigned width);
  const Expr* integerLit(long v, unsigned width);

  string type(const llvm::Type* t);
  string type(const llvm::Value* v);
  
  const Expr* mem(const llvm::Value* v);

  const Expr* lit(const llvm::Value* v);
  const Expr* lit(const llvm::Value* v, unsigned flag);

  const Expr* ptrArith(const llvm::GetElementPtrInst* I);
  const Expr* ptrArith(const llvm::ConstantExpr* CE);
  const Expr* ptrArith(const llvm::Value* p, vector< pair<llvm::Value*,llvm::Type*> > args);

  const Expr* expr(const llvm::Value* v);

  const Expr* cast(const llvm::Instruction* I);
  const Expr* cast(const llvm::ConstantExpr* CE);

  const Expr* bop(const llvm::BinaryOperator* BO);
  const Expr* bop(const llvm::ConstantExpr* CE);

  const Expr* cmp(const llvm::CmpInst* I);
  const Expr* cmp(const llvm::ConstantExpr* CE);

  const Expr* arg(llvm::Function* f, unsigned pos, llvm::Value* v);
  const Stmt* call(llvm::Function* f, const llvm::User& u);
  string code(llvm::CallInst& ci);

  const Stmt* alloca(llvm::AllocaInst& i);
  const Stmt* memcpy(const llvm::MemCpyInst& msi);
  const Stmt* memset(const llvm::MemSetInst& msi);
  const Stmt* load(const llvm::LoadInst& LI);
  const Stmt* store(const llvm::StoreInst& SI);

  vector<Decl*> decl(llvm::Function* F);
  ProcDecl* proc(llvm::Function* f);

  virtual vector<Decl*> globalDecl(const llvm::GlobalValue* g);
  virtual void addBplGlobal(string name);
  virtual vector<string> getModifies();
  unsigned numElements(const llvm::Constant* v);
  void addInitFunc(const llvm::Function* f);
  Decl* getStaticInit();
  Decl* getInitFuncs();
  virtual string getPrelude();

  virtual const Expr* declareIsExternal(const Expr* e);

private:
  virtual Decl* memcpyProc(unsigned dstReg, unsigned srcReg);
  virtual Decl* memsetProc(unsigned dstReg);
};

class RegionCollector : public llvm::InstVisitor<RegionCollector> {
private:
  SmackRep& rep;

public:
  RegionCollector(SmackRep& r) : rep(r) {}
  void visitModule(llvm::Module& M) {
    for (llvm::Module::const_global_iterator
         G = M.global_begin(), E = M.global_end(); G != E; ++G)
      rep.getRegion(G);
  }
  void visitAllocaInst(llvm::AllocaInst& I) {
    rep.getRegion(&I);
  }
  void visitLoadInst(llvm::LoadInst& I) {
    rep.getRegion(I.getPointerOperand());
  }
  void visitStoreInst(llvm::StoreInst& I) {
    rep.getRegion(I.getPointerOperand());
  }
  void visitAtomicCmpXchgInst(llvm::AtomicCmpXchgInst &I) {
    rep.getRegion(I.getPointerOperand());
  }
  void visitAtomicRMWInst(llvm::AtomicRMWInst &I) {
    rep.getRegion(I.getPointerOperand());
  }
  void visitCallInst(llvm::CallInst& I) {
    if (I.getType()->isPointerTy())
      rep.getRegion(&I);
  }
};

}

#endif // SMACKREP_H

