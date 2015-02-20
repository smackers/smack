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
  static const string NULL_VAL;

  static const string ALLOCA;
  static const string MALLOC;
  static const string FREE;
  static const string MEMCPY;

  static const string B2P;
  static const string I2B;
  static const string B2I;
  
  static const string MEM_OP;
  static const string REC_MEM_OP;
  static const string MEM_OP_VAL;

  static const Expr* NUL;
  
  static const string STATIC_INIT;

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

  int globalsBottom;
  int externsBottom;
  vector<const Stmt*> staticInits;
  
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
  void addInit(unsigned region, const Expr* addr, const llvm::Constant* val, const llvm::GlobalValue* V, bool safety);

  const Expr* pa(const Expr* base, int index, int size, int i_size = 0, int t_size = 0);
  const Expr* pa(const Expr* base, const Expr* index, int size, int i_size = 0, int t_size = 0);
  const Expr* pa(const Expr* base, const Expr* index, const Expr* size, int i_size = 0, int t_size = 0);
  
  const Expr* i2b(const llvm::Value* v);
  const Expr* b2i(const llvm::Value* v);

  string indexedName(string name, int idx);
  string indexedName(string name, vector<string> idxs);

public:
  bool isMallocOrFree(const llvm::Function* f);
  bool isIgnore(const llvm::Function* f);
  bool isInt(const llvm::Type* t);
  bool isInt(const llvm::Value* v);
  bool isFloat(const llvm::Type* t);
  bool isFloat(const llvm::Value* v);
  unsigned getElementSize(const llvm::Value* v);
  unsigned getIntSize(const llvm::Value* v);
  unsigned getIntSize(const llvm::Type* t);
  unsigned getSize(llvm::Type* t);

  unsigned storageSize(llvm::Type* t);
  unsigned fieldOffset(llvm::StructType* t, unsigned fieldNo);
  
  unsigned getRegion(const llvm::Value* v);
  string memReg(unsigned i);
  string memType(unsigned region, unsigned size);
  string memPath(unsigned region, unsigned size);
  bool isExternal(const llvm::Value* v);
  void collectRegions(llvm::Module &M);

  string bits_type(unsigned width);
  string int_type(unsigned width);
  virtual string type(const llvm::Type* t);
  virtual string type(const llvm::Value* v);
  
  const Expr* mem(const llvm::Value* v);
  const Expr* mem(unsigned region, const Expr* addr, unsigned size = 0);

  const Expr* lit(const llvm::Value* v);
  const Expr* lit(int v, unsigned size = 0);
  const Expr* lit(const llvm::Value* v, unsigned flag);

  const Expr* ptrArith(const llvm::Value* p, vector<llvm::Value*> ps,
                       vector<llvm::Type*> ts);
  const Expr* expr(const llvm::Value* v);
  string getString(const llvm::Value* v);

  string cast2fn(unsigned opcode);
  string bop2fn(unsigned opcode);
  string armwop2fn(unsigned opcode);
  string pred2fn(unsigned predicate);

  const Expr* cast(const llvm::Instruction* I);
  const Expr* cast(const llvm::ConstantExpr* CE);
  const Expr* cast(unsigned opcode, const llvm::Value* v, const llvm::Type* t);
  string opName(const string& operation, initializer_list<unsigned> operands);

  const Expr* bop(const llvm::BinaryOperator* BO);
  const Expr* bop(const llvm::ConstantExpr* CE);
  const Expr* bop(unsigned opcode, const llvm::Value* lhs, const llvm::Value* rhs, const llvm::Type* t);

  const Expr* cmp(const llvm::CmpInst* I);
  const Expr* cmp(const llvm::ConstantExpr* CE);
  const Expr* cmp(unsigned predicate, const llvm::Value* lhs, const llvm::Value* rhs);

  const Expr* arg(llvm::Function* f, unsigned pos, llvm::Value* v);
  const Stmt* call(llvm::Function* f, llvm::User& u);
  string code(llvm::CallInst& ci);
  ProcDecl* proc(llvm::Function* f);
  ProcDecl* proc(llvm::Function* f, llvm::User* ci);

  virtual const Stmt* alloca(llvm::AllocaInst& i);
  virtual const Stmt* memcpy(const llvm::MemCpyInst& msi);
  virtual const Stmt* memset(const llvm::MemSetInst& msi);
  virtual const Stmt* load(const llvm::Value* addr, const llvm::Value* val);
  virtual const Stmt* store(const llvm::Value* addr, const llvm::Value* val, const llvm::StoreInst* si = NULL);
  virtual const Stmt* storeAsBytes(unsigned region, unsigned size, const Expr* p, const Expr* e);
  bool isFieldDisjoint(const llvm::Value* ptr, const llvm::Instruction* inst);
  bool isFieldDisjoint(const llvm::GlobalValue* V, unsigned offset);
  bool isTypeSafe(const llvm::Value* ptr, const llvm::Instruction* inst);
  bool isTypeSafe(const llvm::GlobalValue* V);
  bool isCollapsed(const llvm::Value* v);
  
  virtual vector<Decl*> globalDecl(const llvm::Value* g);
  virtual void addBplGlobal(string name);
  virtual vector<string> getModifies();
  unsigned numElements(const llvm::Constant* v);
  void addInit(unsigned region, const llvm::Value* addr, const llvm::Constant* val);
  bool hasStaticInits();
  Decl* getStaticInit();
  virtual string getPtrType();
  virtual string getPrelude();

  virtual const Expr* declareIsExternal(const Expr* e);

  virtual string memcpyProc(int dstReg, int srcReg);
  virtual string memsetProc(int dstReg);
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

