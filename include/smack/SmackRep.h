//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACKREP_H
#define SMACKREP_H

#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/Support/GraphWriter.h"
#include "llvm/Support/Regex.h"
#include <sstream>
#include <list>

namespace smack {

class Naming;
class Program;
class Decl;
class ProcDecl;
class Stmt;
class Expr;
class Regions;

using llvm::Regex;
using llvm::SmallVector;
using llvm::StringRef;

class SmackRep {
protected:
  const llvm::DataLayout* targetData;
  Naming* naming;
  Program* program;
  Regions* regions;
  std::vector<std::string> bplGlobals;
  std::map<const llvm::Value*, unsigned> globalAllocations;

  long globalsBottom;
  long externsBottom;
  unsigned uniqueFpNum;
  unsigned ptrSizeInBits;

  std::vector<std::string> initFuncs;
  std::map<std::string, Decl*> auxDecls;

public:
  SmackRep(const llvm::DataLayout* L, Naming* N, Program* P, Regions* R);
  Program* getProgram() { return program; }

private:

  unsigned storageSize(llvm::Type* T);
  unsigned offset(llvm::ArrayType* T, unsigned idx);
  unsigned offset(llvm::StructType* T, unsigned idx);

  const Expr* pa(const Expr* base, long long index, unsigned long size);
  const Expr* pa(const Expr* base, const Expr* index, unsigned long size);
  const Expr* pa(const Expr* base, unsigned long offset);
  const Expr* pa(const Expr* base, const Expr* index, const Expr* size);
  const Expr* pa(const Expr* base, const Expr* offset);

  const Expr* bitConversion(const Expr* e, bool src, bool dst);
  const Expr* pointerToInteger(const Expr* e, unsigned width);
  const Expr* integerToPointer(const Expr* e, unsigned width);

  std::string opName(const std::string& operation, std::initializer_list<const llvm::Type*> types);
  std::string opName(const std::string& operation, std::initializer_list<unsigned> types);

  const Stmt* store(unsigned R, const llvm::Type* T, const Expr* P, const Expr* V);

  const Expr* cast(unsigned opcode, const llvm::Value* v, const llvm::Type* t);
  const Expr* bop(unsigned opcode, const llvm::Value* lhs, const llvm::Value* rhs, const llvm::Type* t);
  const Expr* cmp(unsigned predicate, const llvm::Value* lhs, const llvm::Value* rhs, bool isUnsigned);

  std::string procName(const llvm::User& U);
  std::string procName(llvm::Function* F, const llvm::User& U);
  std::string procName(llvm::Function* F,  std::list<const llvm::Type*> types);

  unsigned getIntSize(const llvm::Value* v);
  unsigned getIntSize(const llvm::Type* t);
  unsigned getSize(llvm::Type* t);

  std::string pointerType();
  std::string intType(unsigned width);

  unsigned numElements(const llvm::Constant* v);

  Decl* memcpyProc(std::string type,
    unsigned length = std::numeric_limits<unsigned>::max());
  Decl* memsetProc(std::string type,
    unsigned length = std::numeric_limits<unsigned>::max());

public:
  const Expr* pointerLit(unsigned v) { return pointerLit((unsigned long) v); }
  const Expr* pointerLit(unsigned long v);
  const Expr* pointerLit(long v);
  const Expr* integerLit(unsigned v, unsigned width) { return integerLit((unsigned long) v, width); }
  const Expr* integerLit(unsigned long v, unsigned width);
  const Expr* integerLit(long v, unsigned width);

  std::string type(const llvm::Type* t);
  std::string type(const llvm::Value* v);

  const Expr* lit(const llvm::Value* v, bool isUnsigned=false);
  const Expr* lit(const llvm::Value* v, unsigned flag);

  const Expr* ptrArith(const llvm::GetElementPtrInst* I);
  const Expr* ptrArith(const llvm::ConstantExpr* CE);
  const Expr* ptrArith(const llvm::Value* p, std::vector< std::pair<llvm::Value*,llvm::Type*> > args);

  const Expr* expr(const llvm::Value* v, bool isConstIntUnsigned=false);

  const Expr* cast(const llvm::Instruction* I);
  const Expr* cast(const llvm::ConstantExpr* CE);

  const Expr* bop(const llvm::BinaryOperator* BO);
  const Expr* bop(const llvm::ConstantExpr* CE);

  const Expr* cmp(const llvm::CmpInst* I);
  const Expr* cmp(const llvm::ConstantExpr* CE);

  const Expr* arg(llvm::Function* f, unsigned pos, llvm::Value* v);
  const Stmt* call(llvm::Function* f, const llvm::User& u);
  std::string code(llvm::CallInst& ci);

  const Stmt* alloca(llvm::AllocaInst& i);
  const Stmt* memcpy(const llvm::MemCpyInst& msi);
  const Stmt* memset(const llvm::MemSetInst& msi);
  const Expr* load(const llvm::Value* P);
  const Stmt* store(const llvm::Value* P, const llvm::Value* V);
  const Stmt* store(const llvm::Value* P, const Expr* V);

  const Stmt* valueAnnotation(const llvm::CallInst& CI);
  const Stmt* returnValueAnnotation(const llvm::CallInst& CI);

  std::list<ProcDecl*> procedure(llvm::Function* F);
  ProcDecl* procedure(llvm::Function* F, llvm::CallInst* C);

  // used in Slicing
  unsigned getElementSize(const llvm::Value* v);

  std::string memReg(unsigned i);
  std::string memType(unsigned region);
  std::string memPath(unsigned region);

  std::list< std::pair< std::string, std::string > > memoryMaps();

  // used in SmackInstGenerator
  std::string getString(const llvm::Value* v);
  bool isExternal(const llvm::Value* v);
  void addBplGlobal(std::string name);

  // used in SmackModuleGenerator
  std::list<Decl*> globalDecl(const llvm::GlobalValue* g);
  void addInitFunc(const llvm::Function* f);
  Decl* getInitFuncs();
  std::string getPrelude();
  const Expr* declareIsExternal(const Expr* e);

  std::list<Decl*> auxiliaryDeclarations() {
    std::list<Decl*> ds;
    for (auto D : auxDecls)
      ds.push_back(D.second);
    return ds;
  }
};

}

#endif // SMACKREP_H
