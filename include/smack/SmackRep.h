//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACKREP_H
#define SMACKREP_H

#include "smack/BoogieAst.h"
#include "smack/DSAAliasAnalysis.h"
#include "smack/Naming.h"
#include "smack/Regions.h"
#include "smack/SmackOptions.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/Support/GraphWriter.h"
#include "llvm/Support/Regex.h"
#include <sstream>

namespace smack {

using llvm::Regex;
using llvm::SmallVector;
using llvm::StringRef;
using namespace std;

class SmackRep {
public:
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
  Regions& regions;
  Naming& naming;
  Program& program;
  vector<string> bplGlobals;
  const llvm::DataLayout* targetData;
  unsigned ptrSizeInBits;

  long globalsBottom;
  long externsBottom;
  vector<const Stmt*> staticInits;
  vector<const Stmt*> initFuncs;

  unsigned uniqueFpNum;

public:
  SmackRep(const DataLayout* L, Naming& N, Program& P, Regions& R)
    : targetData(L), naming(N), program(P), regions(R),
      globalsBottom(0), externsBottom(-32768), uniqueFpNum(0),
      ptrSizeInBits(targetData->getPointerSizeInBits())
  { }
  Program& getProgram() { return program; }

private:
  void addInit(const llvm::GlobalValue* G, const llvm::Constant* C);
  void addInit(const llvm::GlobalValue* G, unsigned offset,
    const llvm::Constant* C);

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

  const Stmt* store(const GlobalValue* P, unsigned offset, const Value* val);
  const Stmt* store(unsigned R, const Type* T, const Expr* P, const Expr* V);

  const Expr* cast(unsigned opcode, const llvm::Value* v, const llvm::Type* t);
  const Expr* bop(unsigned opcode, const llvm::Value* lhs, const llvm::Value* rhs, const llvm::Type* t);
  const Expr* cmp(unsigned predicate, const llvm::Value* lhs, const llvm::Value* rhs);

  string procName(const llvm::User& U);
  string procName(const llvm::User& U, llvm::Function* F);

  unsigned getIntSize(const llvm::Value* v);
  unsigned getIntSize(const llvm::Type* t);
  unsigned getSize(llvm::Type* t);

  string pointerType();
  string intType(unsigned width);

  unsigned numElements(const llvm::Constant* v);

  Decl* memcpyProc(string type,
    unsigned length = std::numeric_limits<unsigned>::max());
  Decl* memsetProc(string type,
    unsigned length = std::numeric_limits<unsigned>::max());

public:
  const Expr* pointerLit(unsigned v) { return pointerLit((unsigned long) v); }
  const Expr* pointerLit(unsigned long v);
  const Expr* pointerLit(long v);
  const Expr* integerLit(unsigned v, unsigned width) { return integerLit((unsigned long) v, width); }
  const Expr* integerLit(unsigned long v, unsigned width);
  const Expr* integerLit(long v, unsigned width);

  string type(const llvm::Type* t);
  string type(const llvm::Value* v);

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
  const Expr* load(const llvm::Value* P);
  const Stmt* store(const Value* P, const Value* V);
  const Stmt* store(const Value* P, const Expr* V);

  const Stmt* valueAnnotation(const CallInst& CI);
  const Stmt* returnValueAnnotation(const CallInst& CI);
  const Stmt* objectAnnotation(const CallInst& CI);
  const Stmt* returnObjectAnnotation(const CallInst& CI);

  vector<Decl*> decl(llvm::Function* F);
  Decl* decl(llvm::Function* F, llvm::CallInst* C);
  vector<ProcDecl*> proc(llvm::Function* F);

  // used in Slicing
  unsigned getElementSize(const llvm::Value* v);

  string memReg(unsigned i);
  string memType(unsigned region);
  string memPath(unsigned region);

  // used in SmackInstGenerator
  string getString(const llvm::Value* v);
  bool isExternal(const llvm::Value* v);
  void addBplGlobal(string name);

  // used in SmackModuleGenerator
  vector<Decl*> globalDecl(const llvm::GlobalValue* g);
  vector<string> getModifies();
  void addInitFunc(const llvm::Function* f);
  Decl* getInitFuncs();
  Decl* getStaticInit();
  string getPrelude();
  const Expr* declareIsExternal(const Expr* e);
};

}

#endif // SMACKREP_H
