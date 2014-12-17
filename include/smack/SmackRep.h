//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACKREP_H
#define SMACKREP_H

#include "smack/Naming.h"
//#define BITVECTOR

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
  static const string BYTE_TYPE;
  static const string LOAD;
  static const string STORE;
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

  // TODO Make this width a parameter to generate bitvector-based code.
  static const int width;
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
  int globalsBottom;
  
  vector<const Stmt*> staticInits;
  
  unsigned uniqueFpNum;

public:
  SmackRep(DSAAliasAnalysis* aa, Naming& N, Program& P)
    : aliasAnalysis(aa), naming(N), program(P),
      targetData(aa->getDataLayout()), globalsBottom(0) {
    uniqueFpNum = 0;
  }
  DSAAliasAnalysis* getAliasAnalysis() { return aliasAnalysis; }
  Program& getProgram() { return program; }

private:
  // 
  // Pointer size: 32
  //
  static const unsigned ptrsize;
  //
  // A flag for bit-vector
  //
  static bool BIT_VECTOR;
  static bool USE_DSA;
  void addInit(unsigned region, const Expr* addr, const llvm::Constant* val, const llvm::GlobalValue* V, bool safety);

  const Expr* pa(const Expr* base, int index, int size);
  const Expr* pa(const Expr* base, const Expr* index, int size);
  const Expr* pa(const Expr* base, const Expr* index, const Expr* size);
  
  const Expr* b2p(const llvm::Value* v);
  const Expr* i2b(const llvm::Value* v);
  const Expr* b2i(const llvm::Value* v);

public:
  //
  // Setter for BIT_VECTOR flag
  //
  void useBitVector();
  //
  // Setter for USE_DSA flag
  //
  void useDSA();
  //
  // Getter for BIT_VECTOR flag
  //
  bool tryBitVector();
  //
  // Getter for USE_DSA flag
  //
  bool tryDSA();

  bool isMallocOrFree(const llvm::Function* f);
  bool isIgnore(const llvm::Function* f);
  bool isInt(const llvm::Type* t);
  bool isInt(const llvm::Value* v);
  bool isBool(const llvm::Type* t);
  bool isBool(const llvm::Value* v);
  bool isFloat(const llvm::Type* t);
  bool isFloat(const llvm::Value* v);
  unsigned getIntSize(const llvm::Value* v);
  unsigned getIntSize(const llvm::Type* t);
  unsigned getPtrSize(const llvm::Value* v);
  unsigned getPtrSize(llvm::Type* t);
  bool isPointer(const llvm::Value* v);
  bool isPointer(const llvm::Type* t);
  virtual string getByteType();

  unsigned storageSize(llvm::Type* t);
  unsigned fieldOffset(llvm::StructType* t, unsigned fieldNo);
  
  unsigned getRegion(const llvm::Value* v);
  string memReg(unsigned i);
  string memReg(unsigned i, bool safety, unsigned type);
  string memType(unsigned r);
  string memType(unsigned r, unsigned type);
  bool isExternal(const llvm::Value* v);
  void collectRegions(llvm::Module &M);

  virtual string type(const llvm::Type* t);
  virtual string type(const llvm::Value* v);
  
  const Expr* mem(const llvm::Value* v);
  const Expr* mem(unsigned region, const Expr* addr);  
  const Expr* mem(const llvm::Value* v, bool safety);
  const Expr* mem(unsigned region, const Expr* addr, bool safety, unsigned type);  

  const Expr* lit(const llvm::Value* v);
  const Expr* lit(int v);
  const Expr* lit(int v, unsigned size);
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
  string bopName(unsigned operand1, unsigned operand2, const string& operation);
  string bopName(unsigned operand1, const string& operation);
  string uopName(unsigned operand, const string& operation, unsigned debug);

  const Expr* bop(const llvm::BinaryOperator* BO);
  const Expr* bop(const llvm::ConstantExpr* CE);
  const Expr* bop(unsigned opcode, const llvm::Value* lhs, const llvm::Value* rhs, const llvm::Type* t);

  const Expr* cmp(const llvm::CmpInst* I);
  const Expr* cmp(const llvm::ConstantExpr* CE);
  const Expr* cmp(unsigned predicate, const llvm::Value* lhs, const llvm::Value* rhs);

  const Expr* arg(llvm::Function* f, unsigned pos, llvm::Value* v);
  const Stmt* call(llvm::Function* f, llvm::User& u);
  string code(llvm::CallInst& ci);
  ProcDecl* proc(llvm::Function* f, int n);

  virtual const Stmt* alloca(llvm::AllocaInst& i);
  virtual const Stmt* memcpy(const llvm::MemCpyInst& msi);
  virtual const Stmt* memset(const llvm::MemSetInst& msi);
  virtual const Stmt* load_bytes(const llvm::LoadInst& li);
  virtual const Stmt* store_bytes(const llvm::StoreInst& si);
  virtual const Stmt* store_bytes(unsigned region, unsigned size, const Expr* p, const Expr* e);
  bool isFieldsOverlap(const llvm::Value* ptr, const llvm::Instruction* inst);
  bool isFieldsOverlap(const llvm::GlobalValue* V, unsigned offset);
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

