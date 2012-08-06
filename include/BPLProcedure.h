//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef BPLPROCEDURE_H_
#define BPLPROCEDURE_H_

#include "BPLBlock.h"
#include "BPLPrintUtils.h"
#include "Utils.h"
#include "llvm/Function.h"
#include "llvm/Support/InstIterator.h"
#include <map>
#include <sstream>

using namespace llvm;

namespace smack {

class AnnoExpr;

class BPLProcedure {
private:
  Function* func;
  std::vector<BPLBlock*> blocks;
  BPLBlock* entryBlock;
  std::vector<Value*> vars;
  std::vector<Value*> boolVars;
  BPLVarExpr* returnVar;
  bool voidFlag;

public:
	BPLProcedure(Function* funcP);
	virtual ~BPLProcedure();
  Function* getFunction() const;
	void setEntryBlock(BPLBlock* block);
  BPLBlock* getEntryBlock() const;
  void addBlock(BPLBlock* block);
  std::vector<BPLBlock*>& getBlocks();
  void addVariable(Value* var);
  void addBoolVariable(Value* var);
  bool isVoid() const;
  BPLVarExpr* getReturnVar() const;
  void print(std::ostream &os) const;
};
std::ostream &operator<<(std::ostream &os, const BPLProcedure* proc);
std::ostream &operator<<(std::ostream &os, const BPLProcedure& proc);

}

#endif /*BPLPROCEDURE_H_*/
